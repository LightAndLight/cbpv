{-# language DataKinds, GADTs, KindSignatures #-}
{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language StandaloneDeriving #-}
module Syntax where

import Control.Lens.Lens (Lens')
import Data.Bifunctor (first)
import Data.List (iterate)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Set (Set)
import Data.Text (Text)

import qualified Data.Set as Set

data Sort = C | V

data IndDecl
  = IndDecl
  { _indTypeName :: !Text
  , _indTypeKind :: Kind
  , _indCtors :: [IndCtor]
  } deriving Show

data IndCtor
  = IndCtor
  { _indCtorName :: !Text
  , _indCtorArity :: !Int
  , _indCtorArgs :: [Ty]
  } deriving Show

class HasIndDecls s where; indDecls :: Lens' s [IndDecl]
instance e ~ IndDecl => HasIndDecls [e] where; indDecls = id

data Kind
  = KArr Kind Kind
  | KComputation
  | KValue
  deriving (Eq, Ord, Show)

unfoldKArr :: Kind -> ([Kind], Kind)
unfoldKArr (KArr a b) = first (a :) $ unfoldKArr b
unfoldKArr a = ([], a)

infixl 5 `TApp`
data Ty where
  -- | f : (a -> b)  /\\   x : a   ==>   f x : b
  TApp :: Ty -> Ty -> Ty
  {-
  inl3 : forall (a : Value). Sum Int a
  inl3 = inl 3

  inl' : forall (a : Value) (b : Value). a -> F (Sum a b)
  inl' = \x -> return (inl x)
  -}
  -- | k1 kind  /\\  k1 |- b : k2  ==>  (  forall (a : k1). b  ) : k2
  TForall :: Maybe Text -> Kind -> Ty -> Ty

  -- value types

  -- | U : CType -> VType
  U :: Ty
  -- | Inductive : ... -> VType
  TInd :: Text -> Ty

  -- computation types

  -- | F : VType -> CType
  F :: Ty
  -- | With : CType -> CType -> CType
  With :: Ty
  -- | Arrow : VType -> CType -> CType
  Arrow :: Ty

  -- | TVar : a
  TVar :: Int -> Ty
  deriving (Eq, Show)

tvars :: Ty -> Set Int
tvars = go
  where
    go (TVar n) = Set.singleton n
    go (TApp a b) = go a <> go b
    go _ = mempty

unfoldTApp :: Ty -> (Ty, [Ty])
unfoldTApp = go []
  where
    go ts (TApp a b) = go (b : ts) a
    go ts b = (b, ts)

renameTy :: (Int -> Int) -> Ty -> Ty
renameTy f t =
  case t of
    U -> U
    TInd a -> TInd a
    TForall n k a -> TForall n k $ renameTy (rho f) a
    F -> F
    With -> With
    Arrow -> Arrow
    TApp a b -> TApp (renameTy f a) (renameTy f b)
    TVar a -> TVar (f a)

sigmaTy :: (Int -> Ty) -> (Int -> Ty)
sigmaTy _ 0 = TVar 0
sigmaTy f n = renameTy (+1) $ f (n-1)

substTy :: (Int -> Ty) -> Ty -> Ty
substTy f t =
  case t of
    U -> U
    TInd a -> TInd a
    TForall n k a -> TForall n k $ substTy (sigmaTy f) a
    F -> F
    With -> With
    Arrow -> Arrow
    TApp a b -> TApp (substTy f a) (substTy f b)
    TVar a -> f a

data Pattern
  = PWild
  | PVar (Maybe Text)
  | PCtor !Text !Int [Text]
  deriving (Eq, Show)

patArity :: Pattern -> Int
patArity PWild = 0
patArity (PVar _) = 1
patArity (PCtor _ n _) = n

patNames :: Pattern -> [Text]
patNames PWild = ["_"]
patNames (PVar n) = maybe ["<unnamed>"] pure n
patNames (PCtor _ arity ns) =
  take arity $ ns <> repeat "<unnamed>"

data Branch = Branch Pattern (Exp 'C)
  deriving Show

data Exp (a :: Sort) where
  Ann :: Exp a -> Ty -> Exp a

  -- values
  Var :: !Int -> Exp 'V
  Thunk :: Exp 'C -> Exp 'V
  --                          VType
  Ctor :: Text -> [Exp 'V] -> Exp 'V

  -- computations
  Return :: Exp 'V -> Exp 'C
  MkWith :: Exp 'C -> Exp 'C -> Exp 'C
  --     VType
  Abs :: Maybe Text -> Ty -> Exp 'C -> Exp 'C
  Bind :: Maybe Text -> Exp 'C -> Exp 'C -> Exp 'C
  Let :: Maybe Text -> Exp 'V -> Exp 'C -> Exp 'C
  Force :: Exp 'V -> Exp 'C
  Case :: Exp 'V -> NonEmpty Branch -> Exp 'C
  Fst :: Exp 'C -> Exp 'C
  Snd :: Exp 'C -> Exp 'C
  App :: Exp 'C -> Exp 'V -> Exp 'C
deriving instance Show (Exp a)

rho :: (Int -> Int) -> (Int -> Int)
rho _ 0 = 0
rho f n = f (n-1) + 1

rename :: (Int -> Int) -> Exp a -> Exp a
rename f c =
  case c of
    Ann a b -> Ann (rename f a) b

    Var a -> Var $ f a
    Thunk a -> Thunk $ rename f a
    Ctor a bs -> Ctor a (rename f <$> bs)

    Return a -> Return $ rename f a
    MkWith a b -> MkWith (rename f a) (rename f b)
    Abs n ty a -> Abs n ty (rename (rho f) a)
    Bind n a b -> Bind n (rename f a) (rename (rho f) b)
    Let n a b -> Let n (rename f a) (rename (rho f) b)
    Force a -> Force $ rename f a
    Case a bs ->
      Case (rename f a) $
      fmap
        (\(Branch p e) ->
           Branch p $ rename (iterate rho f !! patArity p) e)
        bs
    Fst a -> Fst $ rename f a
    Snd a -> Snd $ rename f a
    App a b -> App (rename f a) (rename f b)

sigma :: (Int -> Exp 'V) -> (Int -> Exp 'V)
sigma _ 0 = Var 0
sigma f n = rename (+1) $ f (n-1)

subst :: (Int -> Exp 'V) -> Exp a -> Exp a
subst f c =
  case c of
    Ann a b -> Ann (subst f a) b

    Var a -> f a
    Thunk a -> Thunk $ subst f a
    Ctor a bs -> Ctor a (subst f <$> bs)

    Return a -> Return $ subst f a
    MkWith a b -> MkWith (subst f a) (subst f b)
    Abs n ty a -> Abs n ty $ subst (sigma f) a
    Bind n a b -> Bind n (subst f a) (subst (sigma f) b)
    Let n a b -> Let n (subst f a) (subst (sigma f) b)
    Force a -> Force $ subst f a
    Case a bs ->
      Case (subst f a) $
      fmap
        (\(Branch p e) ->
           Branch p $ subst (iterate sigma f !! patArity p) e)
        bs
    Fst a -> Fst $ subst f a
    Snd a -> Snd $ subst f a
    App a b -> App (subst f a) (subst f b)

inst :: Exp a -> Exp 'V -> Exp a
inst a b = subst (\x -> if x == 0 then b else Var (x-1)) a
