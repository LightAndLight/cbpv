{-# language DataKinds, GADTs, KindSignatures #-}
{-# language StandaloneDeriving #-}
module Syntax where

import Control.Monad (unless)

data Sort = C | V

data Ty (a :: Sort) where
  -- value types
  U :: Ty 'C -> Ty 'V
  Zero :: Ty 'V
  Sum :: Ty 'V -> Ty 'V -> Ty 'V
  One :: Ty 'V
  Prod :: Ty 'V -> Ty 'V -> Ty 'V

  -- computation types
  F :: Ty 'V -> Ty 'C
  With :: Ty 'C -> Ty 'C -> Ty 'C
  Arrow :: Ty 'V -> Ty 'C -> Ty 'C
deriving instance Eq (Ty a)
deriving instance Show (Ty a)

data Exp (a :: Sort) where
  -- values
  Var :: !Int -> Exp 'V
  Thunk :: Exp 'C -> Exp 'V
  Inl :: Exp 'V -> Ty 'V -> Exp 'V
  Inr :: Ty 'V -> Exp 'V -> Exp 'V
  MkProd :: Exp 'V -> Exp 'V -> Exp 'V
  MkOne :: Exp 'V

  -- computations
  Return :: Exp 'V -> Exp 'C
  MkWith :: Exp 'C -> Exp 'C -> Exp 'C
  Abs :: Ty 'V -> Exp 'C -> Exp 'C
  Bind :: Exp 'C -> Exp 'C -> Exp 'C
  Let :: Exp 'V -> Exp 'C -> Exp 'C
  Force :: Exp 'V -> Exp 'C
  SumElim :: Exp 'C -> Exp 'C -> Exp 'V -> Exp 'C
  ProdElim :: Exp 'C -> Exp 'V -> Exp 'C
  Fst :: Exp 'C -> Exp 'C
  Snd :: Exp 'C -> Exp 'C
  App :: Exp 'C -> Exp 'V -> Exp 'C
deriving instance Eq (Exp a)
deriving instance Show (Exp a)

data TypeError
  = ExpectedF (Ty 'C)
  | ExpectedU (Ty 'V)
  | ExpectedSum (Ty 'V)
  | ExpectedProd (Ty 'V)
  | ExpectedWith (Ty 'C)
  | ExpectedArrow (Ty 'C)
  | TypeMismatchC (Ty 'C) (Ty 'C)
  | TypeMismatchV (Ty 'V) (Ty 'V)
  | NotInScope Int
  deriving (Eq, Show)

rho :: (Int -> Int) -> (Int -> Int)
rho _ 0 = 0
rho f n = f (n-1) + 1

rename :: (Int -> Int) -> Exp a -> Exp a
rename f c =
  case c of
    Var a -> Var $ f a
    Thunk a -> Thunk $ rename f a
    Inl a ty -> Inl (rename f a) ty
    Inr ty a -> Inr ty (rename f a)
    MkProd a b -> MkProd (rename f a) (rename f b)
    MkOne -> MkOne

    Return a -> Return $ rename f a
    MkWith a b -> MkWith (rename f a) (rename f b)
    Abs ty a -> Abs ty (rename (rho f) a)
    Bind a b -> Bind (rename f a) (rename (rho f) b)
    Let a b -> Let (rename f a) (rename (rho f) b)
    Force a -> Force $ rename f a
    SumElim g h a -> SumElim (rename (rho f) g) (rename (rho f) h) (rename f a)
    ProdElim g a -> ProdElim (rename (rho f) g) (rename f a)
    Fst a -> Fst $ rename f a
    Snd a -> Snd $ rename f a
    App a b -> App (rename f a) (rename f b)

sigma :: (Int -> Exp 'V) -> (Int -> Exp 'V)
sigma _ 0 = Var 0
sigma f n = rename (+1) $ f (n-1)

subst :: (Int -> Exp 'V) -> Exp a -> Exp a
subst f c =
  case c of
    Var a -> f a
    Thunk a -> Thunk $ subst f a
    Inl a ty -> Inl (subst f a) ty
    Inr ty a -> Inr ty (subst f a)
    MkProd a b -> MkProd (subst f a) (subst f b)
    MkOne -> MkOne

    Return a -> Return $ subst f a
    MkWith a b -> MkWith (subst f a) (subst f b)
    Abs ty a -> Abs ty (subst (sigma f) a)
    Bind a b -> Bind (subst f a) (subst (sigma f) b)
    Let a b -> Let (subst f a) (subst (sigma f) b)
    Force a -> Force $ subst f a
    SumElim g h a -> SumElim (subst (sigma f) g) (subst (sigma f) h) (subst f a)
    ProdElim g a -> ProdElim (subst (sigma f) g) (subst f a)
    Fst a -> Fst $ subst f a
    Snd a -> Snd $ subst f a
    App a b -> App (subst f a) (subst f b)

inst :: Exp a -> Exp 'V -> Exp a
inst a b = subst (\x -> if x == 0 then b else Var (x-1)) a

ix :: Int -> [a] -> Maybe a
ix _ [] = Nothing
ix 0 (x:_) = Just x
ix n (_:xs) = ix (n-1) xs

infer :: [Ty 'V] -> Exp a -> Either TypeError (Ty a)
infer ctx c =
  case c of
    Var n ->
      case ix n ctx of
        Nothing -> Left $ NotInScope n
        Just t -> pure t
    Thunk a -> U <$> infer ctx a
    Inl a ty -> Sum <$> infer ctx a <*> pure ty
    Inr ty a -> Sum ty <$> infer ctx a
    MkProd a b -> Prod <$> infer ctx a <*> infer ctx b
    MkOne -> pure One

    Return a -> F <$> infer ctx a
    MkWith a b -> With <$> infer ctx a <*> infer ctx b
    Abs ty a -> Arrow ty <$> infer ctx a
    Bind a b -> do
      aTy <- infer ctx a
      case aTy of
        F i -> infer (i : ctx) b
        _ -> Left $ ExpectedF aTy
    Let a b -> do
      aTy <- infer ctx a
      infer (aTy : ctx) b
    Force a -> do
      aTy <- infer ctx a
      case aTy of
        U i -> pure i
        _ -> Left $ ExpectedU aTy
    SumElim f g a -> do
      aTy <- infer ctx a
      case aTy of
        Sum x y -> do
          fTy <- infer (x : ctx) f
          gTy <- infer (y : ctx) g
          unless (fTy == gTy) . Left $ TypeMismatchC fTy gTy
          pure fTy
        _ -> Left $ ExpectedSum aTy
    ProdElim f a -> do
      aTy <- infer ctx a
      case aTy of
        Prod x y -> infer (x : y : ctx) f
        _ -> Left $ ExpectedProd aTy
    Fst a -> do
      aTy <- infer ctx a
      case aTy of
        With x _ -> pure x
        _ -> Left $ ExpectedWith aTy
    Snd a -> do
      aTy <- infer ctx a
      case aTy of
        With _ y -> pure y
        _ -> Left $ ExpectedWith aTy
    App f x -> do
      fTy <- infer ctx f
      case fTy of
        Arrow a b -> do
          xTy <- infer ctx x
          unless (a == xTy) . Left $ TypeMismatchV a xTy
          pure b
        _ -> Left $ ExpectedArrow fTy
