{-# language DataKinds, GADTs #-}
module Syntax where

import Control.Monad (unless)

data Sort = C | V

data TyV
  = U TyC
  | Zero
  | Sum TyV TyV
  | One
  | Prod TyV TyV
  deriving (Eq, Show)

data TyC
  = F TyV
  | With TyC TyC
  | Arrow TyV TyC
  deriving (Eq, Show)

data V
  = Var !Int
  | Thunk C
  | Inl V TyV
  | Inr TyV V
  | MkProd V V
  | MkOne
  deriving (Eq, Show)

data C
  = Return V
  | MkWith C C
  | Abs TyV C
  | Bind C C
  | Force V
  | SumElim C C V
  | ProdElim C V
  | Fst C
  | Snd C
  | App C V
  deriving (Eq, Show)

data TypeError
  = ExpectedF TyC
  | ExpectedU TyV
  | ExpectedSum TyV
  | ExpectedProd TyV
  | ExpectedWith TyC
  | ExpectedArrow TyC
  | TypeMismatchC TyC TyC
  | TypeMismatchV TyV TyV
  | NotInScope Int
  deriving (Eq, Show)

rho :: (Int -> Int) -> (Int -> Int)
rho _ 0 = 0
rho f n = f (n-1) + 1

renameC :: (Int -> Int) -> C -> C
renameC f c =
  case c of
    Return a -> Return $ renameV f a
    MkWith a b -> MkWith (renameC f a) (renameC f b)
    Abs ty a -> Abs ty (renameC (rho f) a)
    Bind a b -> Bind (renameC f a) (renameC (rho f) b)
    Force a -> Force $ renameV f a
    SumElim g h a -> SumElim (renameC (rho f) g) (renameC (rho f) h) (renameV f a)
    ProdElim g a -> ProdElim (renameC (rho f) g) (renameV f a)
    Fst a -> Fst $ renameC f a
    Snd a -> Snd $ renameC f a
    App a b -> App (renameC f a) (renameV f b)

renameV :: (Int -> Int) -> V -> V
renameV f v =
  case v of
    Var a -> Var $ f a
    Thunk a -> Thunk $ renameC f a
    Inl a ty -> Inl (renameV f a) ty
    Inr ty a -> Inr ty (renameV f a)
    MkProd a b -> MkProd (renameV f a) (renameV f b)
    MkOne -> MkOne

sigma :: (Int -> V) -> (Int -> V)
sigma _ 0 = Var 0
sigma f n = renameV (+1) $ f (n-1)

substC :: (Int -> V) -> C -> C
substC f c =
  case c of
    Return a -> Return $ substV f a
    MkWith a b -> MkWith (substC f a) (substC f b)
    Abs ty a -> Abs ty (substC (sigma f) a)
    Bind a b -> Bind (substC f a) (substC (sigma f) b)
    Force a -> Force $ substV f a
    SumElim g h a -> SumElim (substC (sigma f) g) (substC (sigma f) h) (substV f a)
    ProdElim g a -> ProdElim (substC (sigma f) g) (substV f a)
    Fst a -> Fst $ substC f a
    Snd a -> Snd $ substC f a
    App a b -> App (substC f a) (substV f b)

substV :: (Int -> V) -> V -> V
substV f v =
  case v of
    Var a -> f a
    Thunk a -> Thunk $ substC f a
    Inl a ty -> Inl (substV f a) ty
    Inr ty a -> Inr ty (substV f a)
    MkProd a b -> MkProd (substV f a) (substV f b)
    MkOne -> MkOne

instC :: C -> V -> C
instC a b = substC (\x -> if x == 0 then b else Var (x-1)) a

inferC :: [TyV] -> C -> Either TypeError TyC
inferC ctx c =
  case c of
    Return a -> F <$> inferV ctx a
    MkWith a b -> With <$> inferC ctx a <*> inferC ctx b
    Abs ty a -> Arrow ty <$> inferC ctx a
    Bind a b -> do
      aTy <- inferC ctx a
      case aTy of
        F i -> inferC (i : ctx) b
        _ -> Left $ ExpectedF aTy
    Force a -> do
      aTy <- inferV ctx a
      case aTy of
        U i -> pure i
        _ -> Left $ ExpectedU aTy
    SumElim f g a -> do
      aTy <- inferV ctx a
      case aTy of
        Sum x y -> do
          fTy <- inferC (x : ctx) f
          gTy <- inferC (y : ctx) g
          unless (fTy == gTy) . Left $ TypeMismatchC fTy gTy
          pure fTy
        _ -> Left $ ExpectedSum aTy
    ProdElim f a -> do
      aTy <- inferV ctx a
      case aTy of
        Prod x y -> inferC (x : y : ctx) f
        _ -> Left $ ExpectedProd aTy
    Fst a -> do
      aTy <- inferC ctx a
      case aTy of
        With x _ -> pure x
        _ -> Left $ ExpectedWith aTy
    Snd a -> do
      aTy <- inferC ctx a
      case aTy of
        With _ y -> pure y
        _ -> Left $ ExpectedWith aTy
    App f x -> do
      fTy <- inferC ctx f
      case fTy of
        Arrow a b -> do
          xTy <- inferV ctx x
          unless (a == xTy) . Left $ TypeMismatchV a xTy
          pure b
        _ -> Left $ ExpectedArrow fTy

ix :: Int -> [a] -> Maybe a
ix _ [] = Nothing
ix 0 (x:_) = Just x
ix n (_:xs) = ix (n-1) xs

inferV :: [TyV] -> V -> Either TypeError TyV
inferV ctx v =
  case v of
    Var n ->
      case ix n ctx of
        Nothing -> Left $ NotInScope n
        Just t -> pure t
    Thunk a -> U <$> inferC ctx a
    Inl a ty -> Sum <$> inferV ctx a <*> pure ty
    Inr ty a -> Sum ty <$> inferV ctx a
    MkProd a b -> Prod <$> inferV ctx a <*> inferV ctx b
    MkOne -> pure One
