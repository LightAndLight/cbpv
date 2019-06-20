{-# language BangPatterns #-}
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

data CoIndDecl
  = CoIndDecl
  { _coIndTypeName :: !Text
  , _coIndTypeKind :: Kind
  , _coIndDtors :: [CoIndDtor]
  } deriving Show

data CoIndDtor
  = CoIndDtor
  { _coIndDtorName :: !Text
  , _coIndDtorType :: Ty
  } deriving Show

class HasCoIndDecls s where; coIndDecls :: Lens' s [CoIndDecl]
instance e ~ CoIndDecl => HasCoIndDecls [e] where; coIndDecls = id

data Kind
  = KArr Kind Kind
  | KComp
  | KVal
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

  -- computation types

  -- | F : VType -> CType
  F :: Ty
  -- | Arrow : VType -> CType -> CType
  Arrow :: Ty

  -- | TVar : a
  TVar :: Int -> Ty
  TName :: Text -> Ty
  -- | SomeCtor : a
  TCtor :: Text -> Ty
  deriving (Eq, Show)

abstractTy :: Text -> Ty -> Ty
abstractTy n = go 0
  where
    go !depth ty =
      case ty of
        TApp a b -> TApp (go depth a) (go depth b)
        TForall name k a -> TForall name k $ go (depth+1) a
        TName n' | n == n' -> TVar depth
        TVar ix -> if ix >= depth then TVar (ix + 1) else TVar ix
        _ -> ty

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
    TCtor a -> TCtor a
    TForall n k a -> TForall n k $ renameTy (rho f) a
    F -> F
    Arrow -> Arrow
    TApp a b -> TApp (renameTy f a) (renameTy f b)
    TVar a -> TVar (f a)
    TName a -> TName a

sigmaTy :: (Int -> Ty) -> (Int -> Ty)
sigmaTy _ 0 = TVar 0
sigmaTy f n = renameTy (+1) $ f (n-1)

substTy :: (Int -> Ty) -> Ty -> Ty
substTy f t =
  case t of
    U -> U
    TCtor a -> TCtor a
    TForall n k a -> TForall n k $ substTy (sigmaTy f) a
    F -> F
    Arrow -> Arrow
    TApp a b -> TApp (substTy f a) (substTy f b)
    TVar a -> f a
    TName a -> TName a

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

data Branch a = Branch Pattern (Exp a)
  deriving Show

data CoBranch = CoBranch Text (Exp 'C)
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
  --     VType
  Abs :: Maybe Text -> Ty -> Exp 'C -> Exp 'C
  Bind :: Maybe Text -> Exp 'C -> Exp 'C -> Exp 'C
  Let :: Maybe Text -> Exp 'V -> Exp a -> Exp a
  Fix :: Exp 'C -> Exp 'C
  Force :: Exp 'V -> Exp 'C
  Case :: Exp 'V -> NonEmpty (Branch a) -> Exp a
  CoCase :: Ty -> NonEmpty CoBranch -> Exp 'C
  Dtor :: Text -> Exp 'C -> Exp 'C
  App :: Exp 'C -> Exp 'V -> Exp 'C

  Name :: Text -> Exp 'V
  AbsTy :: Maybe Text -> Kind -> Exp a -> Exp a
  AppTy :: Exp a -> Ty -> Exp a
deriving instance Show (Exp a)

abstract :: Text -> Exp a -> Exp a
abstract n = go 0
  where
    go :: Int -> Exp a -> Exp a
    go !depth tm =
      case tm of
        App a b -> App (go depth a) (go depth b)
        Abs name k a -> Abs name k $ go (depth+1) a
        Bind name v a -> Bind name (go depth v) $ go (depth+1) a
        Let name v a -> Let name (go depth v) $ go (depth+1) a
        Fix a -> Fix $ go (depth+1) a
        Name n'
          | n == n' -> Var depth
          | otherwise -> Name n'
        Var ix -> if ix >= depth then Var (ix + 1) else Var ix
        Ann a b -> Ann (go depth a) b
        Thunk a -> Thunk $ go depth a
        Force a -> Force $ go depth a
        Return a -> Return $ go depth a
        Ctor a b -> Ctor a $ go depth <$> b
        Dtor a b -> Dtor a $ go depth b
        Case a bs ->
          Case
            (go depth a)
            ((\(Branch p e) -> Branch p $ go (depth + patArity p) e) <$> bs)
        CoCase a bs ->
          CoCase a $ (\(CoBranch b c) -> CoBranch b $ go depth c) <$> bs
        AbsTy name k a -> AbsTy name k $ go depth a
        AppTy a t -> AppTy (go depth a) t

abstractTyExp :: Text -> Exp a -> Exp a
abstractTyExp n = go 0
  where
    goTy !depth ty =
      case ty of
        TApp a b -> TApp (goTy depth a) (goTy depth b)
        TForall name k a -> TForall name k $ goTy (depth+1) a
        TName n' | n == n' -> TVar depth
        TVar ix -> if ix >= depth then TVar (ix + 1) else TVar ix
        _ -> ty

    go :: Int -> Exp a -> Exp a
    go !depth tm =
      case tm of
        App a b -> App (go depth a) (go depth b)
        Abs name t a -> Abs name (goTy depth t) (go depth a)
        Bind name v a -> Bind name (go depth v) (go depth a)
        Let name v a -> Let name (go depth v) (go depth a)
        Fix a -> Fix $ go depth a
        Name a -> Name a
        Var ix -> Var ix
        Ann a t -> Ann (go depth a) (goTy depth t)
        Thunk a -> Thunk $ go depth a
        Force a -> Force $ go depth a
        Return a -> Return $ go depth a
        Ctor a b -> Ctor a $ go depth <$> b
        Dtor a b -> Dtor a $ go depth b
        Case a bs ->
          Case
            (go depth a)
            ((\(Branch p e) -> Branch p $ go (depth + patArity p) e) <$> bs)
        CoCase a bs ->
          CoCase (goTy depth a) $ (\(CoBranch b c) -> CoBranch b $ go depth c) <$> bs
        AbsTy name k a -> AbsTy name k $ go (depth+1) a
        AppTy a t -> AppTy (go depth a) (goTy depth t)

rho :: (Int -> Int) -> (Int -> Int)
rho _ 0 = 0
rho f n = f (n-1) + 1

rename :: (Int -> Int) -> Exp a -> Exp a
rename f c =
  case c of
    Ann a b -> Ann (rename f a) b

    Name a -> Name a
    Var a -> Var $ f a
    Thunk a -> Thunk $ rename f a
    Ctor a bs -> Ctor a (rename f <$> bs)

    Return a -> Return $ rename f a
    Abs n ty a -> Abs n ty (rename (rho f) a)
    Bind n a b -> Bind n (rename f a) (rename (rho f) b)
    Let n a b -> Let n (rename f a) (rename (rho f) b)
    Fix a -> Fix $ rename (rho f) a
    Force a -> Force $ rename f a
    Case a bs ->
      Case (rename f a) $
      fmap
        (\(Branch p e) ->
           Branch p $ rename (iterate rho f !! patArity p) e)
        bs
    Dtor a b -> Dtor a $ rename f b
    CoCase a bs ->
      CoCase a $ (\(CoBranch b e) -> CoBranch b $ rename f e) <$> bs
    App a b -> App (rename f a) (rename f b)

    AbsTy n k a -> AbsTy n k $ rename f a
    AppTy a t -> AppTy (rename f a) t

renameTyExp :: (Int -> Int) -> Exp a -> Exp a
renameTyExp f c =
  case c of
    Ann a b -> Ann (renameTyExp f a) (renameTy f b)

    Name a -> Name a
    Var a -> Var a
    Thunk a -> Thunk $ renameTyExp f a
    Ctor a bs -> Ctor a (renameTyExp f <$> bs)

    Return a -> Return $ renameTyExp f a
    Abs n ty a -> Abs n (renameTy f ty) (renameTyExp f a)
    Bind n a b -> Bind n (renameTyExp f a) (renameTyExp f b)
    Let n a b -> Let n (renameTyExp f a) (renameTyExp f b)
    Fix a -> Fix $ renameTyExp f a
    Force a -> Force $ renameTyExp f a
    Case a bs ->
      Case (renameTyExp f a) $
      (\(Branch p e) -> Branch p $ renameTyExp f e) <$> bs
    Dtor n b -> Dtor n $ renameTyExp f b
    CoCase t bs ->
      CoCase (renameTy f t) $
      (\(CoBranch b e) -> CoBranch b $ renameTyExp f e) <$> bs
    App a b -> App (renameTyExp f a) (renameTyExp f b)

    AbsTy n k a -> AbsTy n k $ renameTyExp (rho f) a
    AppTy a t -> AppTy (renameTyExp f a) (renameTy f t)

sigma :: (Int -> Exp 'V) -> (Int -> Exp 'V)
sigma _ 0 = Var 0
sigma f n = rename (+1) $ f (n-1)

subst :: (Int -> Exp 'V) -> Exp a -> Exp a
subst f c =
  case c of
    Ann a b -> Ann (subst f a) b

    Name a -> Name a
    Var a -> f a
    Thunk a -> Thunk $ subst f a
    Ctor a bs -> Ctor a (subst f <$> bs)

    Return a -> Return $ subst f a
    Abs n ty a -> Abs n ty $ subst (sigma f) a
    Bind n a b -> Bind n (subst f a) (subst (sigma f) b)
    Let n a b -> Let n (subst f a) (subst (sigma f) b)
    Fix a -> Fix $ subst (sigma f) a
    Force a -> Force $ subst f a
    Case a bs ->
      Case (subst f a) $
      fmap
        (\(Branch p e) ->
           Branch p $ subst (iterate sigma f !! patArity p) e)
        bs
    Dtor a b -> Dtor a $ subst f b
    CoCase a bs ->
      CoCase a $ (\(CoBranch b e) -> CoBranch b $ subst f e) <$> bs
    App a b -> App (subst f a) (subst f b)

    AbsTy n k a -> AbsTy n k $ subst f a
    AppTy a t -> AppTy (subst f a) t

substTyExp :: (Int -> Ty) -> Exp a -> Exp a
substTyExp f c =
  case c of
    Ann a b -> Ann (substTyExp f a) (substTy f b)

    Name a -> Name a
    Var a -> Var a
    Thunk a -> Thunk $ substTyExp f a
    Ctor a bs -> Ctor a (substTyExp f <$> bs)

    Return a -> Return $ substTyExp f a
    Abs n ty a -> Abs n (substTy f ty) (substTyExp f a)
    Bind n a b -> Bind n (substTyExp f a) (substTyExp f b)
    Let n a b -> Let n (substTyExp f a) (substTyExp f b)
    Fix a -> Fix $ substTyExp f a
    Force a -> Force $ substTyExp f a
    Case a bs ->
      Case (substTyExp f a) $
      (\(Branch p e) -> Branch p $ substTyExp f e) <$> bs
    Dtor n b -> Dtor n $ substTyExp f b
    CoCase t bs ->
      CoCase (substTy f t) $
      (\(CoBranch b e) -> CoBranch b $ substTyExp f e) <$> bs
    App a b -> App (substTyExp f a) (substTyExp f b)

    AbsTy n k a -> AbsTy n k $ substTyExp (sigmaTy f) a
    AppTy a t -> AppTy (substTyExp f a) (substTy f t)

inst :: Exp a -> Exp 'V -> Exp a
inst a b = subst (\x -> if x == 0 then b else Var (x-1)) a

instTyExp :: Exp a -> Ty -> Exp a
instTyExp a b = substTyExp (\x -> if x == 0 then b else TVar (x-1)) a
