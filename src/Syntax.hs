{-# language BangPatterns #-}
{-# language DataKinds, GADTs, KindSignatures #-}
{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Syntax where

import Control.Lens.Getter (view)
import Control.Lens.Lens (Lens')
import Control.Lens.Review ((#))
import Control.Lens.Setter (locally)
import Control.Lens.TH (makeClassyPrisms, makeLenses, makePrisms)
import Control.Monad (unless)
import Control.Monad.Except
  (MonadError, runExcept, throwError, catchError)
import Control.Monad.Reader (MonadReader, runReaderT, asks)
import Data.Bifunctor (first)
import Data.Foldable (traverse_, for_)
import Data.List (iterate)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Semigroup.Foldable (foldlM1)
import Data.Set (Set)
import Data.Text (Text)
import Data.Traversable (for)

import qualified Data.Set as Set

data Sort = C | V

data ScopeError
  = InductiveNotInScope Text
  | CtorNotInScope Text
  deriving Show

data TypeError
  = ExpectedF Ty
  | ExpectedU Ty
  | ExpectedSum Ty
  | ExpectedProd Ty
  | ExpectedWith Ty
  | ExpectedArrow Ty
  | ExpectedInductive Ty
  | TypeMismatch Ty Ty
  | NotInScope Int
  | CtorExpectedArity Int Int
  | Can'tInfer (Exp 'V)
  deriving Show

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
  | KCType
  | KVType
  deriving (Eq, Ord, Show)

unfoldKArr :: Kind -> ([Kind], Kind)
unfoldKArr (KArr a b) = first (a :) $ unfoldKArr b
unfoldKArr a = ([], a)

infixl 5 `TApp`
data Ty where
  -- | f : (a -> b)  /\\   x : a   ==>   f x : b
  TApp :: Ty -> Ty -> Ty

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


substTy :: (Int -> Ty) -> Ty -> Ty
substTy f t =
  case t of
    U -> U
    TInd a -> TInd a
    F -> F
    With -> With
    Arrow -> Arrow
    TApp a b -> TApp (substTy f a) (substTy f b)
    TVar a -> f a

data Pattern
  = PWild
  | PVar
  | PCtor !Text !Int
  deriving (Eq, Show)

patArity :: Pattern -> Int
patArity PWild = 0
patArity PVar = 1
patArity (PCtor _ n) = n

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
  Abs :: Ty -> Exp 'C -> Exp 'C
  Bind :: Exp 'C -> Exp 'C -> Exp 'C
  Let :: Exp 'V -> Exp 'C -> Exp 'C
  Force :: Exp 'V -> Exp 'C
  Case :: Exp 'V -> NonEmpty Branch -> Exp 'C
  Fst :: Exp 'C -> Exp 'C
  Snd :: Exp 'C -> Exp 'C
  App :: Exp 'C -> Exp 'V -> Exp 'C
deriving instance Show (Exp a)

makeClassyPrisms ''TypeError
makeClassyPrisms ''ScopeError

lookupIndDecl ::
  (HasIndDecls r, MonadReader r m, AsScopeError e, MonadError e m) =>
  Text -> m IndDecl
lookupIndDecl a =
  go <$> view indDecls >>=
  maybe (throwError $ _InductiveNotInScope # a) pure
  where
    go [] = Nothing
    go (i : is) =
      if _indTypeName i == a
      then Just i
      else go is

lookupIndCtor ::
  (AsScopeError e, MonadError e m) => Text -> [IndCtor] -> m IndCtor
lookupIndCtor a cs =
  maybe (throwError $ _CtorNotInScope # a) pure $ go cs
  where
    go [] = Nothing
    go (i : is) =
      if _indCtorName i == a
      then Just i
      else go is

findIndCtor ::
  (HasIndDecls r, MonadReader r m, AsScopeError e, MonadError e m) =>
  Text -> m (IndDecl, IndCtor)
findIndCtor a = view indDecls >>= go
  where
    go [] = throwError $ _CtorNotInScope # a
    go (t : ts) =
      catchError
        ((,) t <$> lookupIndCtor a (_indCtors t))
        (\_ -> go ts)

data KindError
  = ExpectedCType Kind
  | ExpectedVType Kind
  | ExpectedKArr Kind
  | KindMismatch Kind Kind
  | TypeNotInScope Int
  | TypeInductiveNotInScope Text
  deriving (Eq, Ord, Show)

makeClassyPrisms ''KindError

ix :: Int -> [a] -> Maybe a
ix _ [] = Nothing
ix 0 (x:_) = Just x
ix n (_:xs) = ix (n-1) xs

data TCEnv
  = TCEnv
  { _envTypes :: [Ty]
  , _envKinds :: [Kind]
  , _envIndDecls :: [IndDecl]
  }
makeLenses ''TCEnv

instance HasIndDecls TCEnv where; indDecls = envIndDecls

inferKind ::
  (AsScopeError e, AsKindError e, MonadError e m, MonadReader TCEnv m) =>
  Ty -> m Kind
inferKind ty =
  case ty of
    U -> pure $ KArr KCType KVType
    TInd n -> do
      decl <- lookupIndDecl n
      pure $ _indTypeKind decl
    F -> pure $ KArr KVType KCType
    With -> pure $ KArr KCType (KArr KCType KCType)
    Arrow -> pure $ KArr KVType (KArr KCType KCType)
    TVar n -> do
      kctx <- asks _envKinds
      case ix n kctx of
        Nothing -> throwError $ _TypeNotInScope # n
        Just k -> pure k
    TApp a b -> do
      aKind <- inferKind a
      case aKind of
        KArr x y -> y <$ checkKind b x
        _ -> throwError $ _ExpectedKArr # aKind

checkKind ::
  (AsScopeError e, AsKindError e, MonadError e m, MonadReader TCEnv m) =>
  Ty -> Kind -> m ()
checkKind ty k = do
  k' <- inferKind ty
  unless (k == k') . throwError $ _KindMismatch # (k, k')

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
    Abs ty a -> Abs ty (rename (rho f) a)
    Bind a b -> Bind (rename f a) (rename (rho f) b)
    Let a b -> Let (rename f a) (rename (rho f) b)
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
    Abs ty a -> Abs ty (subst (sigma f) a)
    Bind a b -> Bind (subst f a) (subst (sigma f) b)
    Let a b -> Let (subst f a) (subst (sigma f) b)
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

checkCtor ::
  (AsScopeError e, AsKindError e, AsTypeError e, MonadError e m, MonadReader TCEnv m) =>
  Text -> [Exp 'V] ->
  Ty -> m ()
checkCtor name args ty =
  case unfoldTApp ty of
    (TInd tname, targs) -> do
      decl <- lookupIndDecl tname
      ctor <- lookupIndCtor name (_indCtors decl)
      let
        actualArity = length args
        expectedArity = _indCtorArity ctor
      unless (expectedArity == actualArity) . throwError $
        _CtorExpectedArity # (expectedArity, actualArity)
      let instTys = substTy (targs !!) <$> _indCtorArgs ctor
      traverse_ (uncurry check) (zip args instTys)
    _ -> throwError $ _ExpectedInductive # ty

check ::
  (AsScopeError e, AsKindError e, AsTypeError e, MonadError e m, MonadReader TCEnv m) =>
  Exp a -> Ty -> m ()
check a ty =
  case a of
    Ctor n as -> checkCtor n as ty
    _ -> do
      aTy <- infer a
      unless (aTy == ty) . throwError $ _TypeMismatch # (ty, aTy)

checkPattern ::
  (AsScopeError e, AsKindError e, AsTypeError e, MonadError e m, MonadReader TCEnv m) =>
  Pattern -> Ty -> m [Ty]
checkPattern PWild _ = pure []
checkPattern PVar ty = pure [ty]
checkPattern (PCtor n act) ty =
  case unfoldTApp ty of
    (TInd nty, targs) -> do
      decl <- lookupIndDecl nty
      ctor <- lookupIndCtor n $ _indCtors decl
      let ex = _indCtorArity ctor
      unless (ex == act) . throwError $ _CtorExpectedArity # (ex, act)
      pure $ substTy (targs !!) <$> _indCtorArgs ctor
    _ -> throwError $ _ExpectedInductive # ty

infer ::
  (AsScopeError e, AsTypeError e, AsKindError e, MonadError e m, MonadReader TCEnv m) =>
  Exp a -> m Ty
infer c =
  case c of
    Var n -> do
      ctx <- asks _envTypes
      case ix n ctx of
        Nothing -> throwError $ _NotInScope # n
        Just t -> pure t
    Thunk a -> TApp U <$> infer a
    Return a -> TApp F <$> infer a
    MkWith a b -> (\x -> TApp (TApp With x)) <$> infer a <*> infer b
    Abs ty a -> do
      checkKind ty KVType
      TApp (TApp Arrow ty) <$> locally envTypes (ty :) (infer a)
    Bind a b -> do
      aTy <- infer a
      case aTy of
        TApp F i -> locally envTypes (i :) $ infer b
        _ -> throwError $ _ExpectedF # aTy
    Let a b -> do
      aTy <- infer a
      locally envTypes (aTy :) $ infer b
    Force a -> do
      aTy <- infer a
      case aTy of
        TApp U i -> pure i
        _ -> throwError $ _ExpectedU # aTy
    Case a bs -> do
      aTy <- infer a
      ts <- for bs $ \(Branch p b) -> do
        vs <- checkPattern p aTy
        locally envTypes (vs <>) $ infer b
      foldlM1
        (\x y -> do
           unless (x == y) . throwError $ _TypeMismatch # (x, y)
           pure x)
        ts
    Fst a -> do
      aTy <- infer a
      case aTy of
        TApp (TApp With x) _ -> pure x
        _ -> throwError $ _ExpectedWith # aTy
    Snd a -> do
      aTy <- infer a
      case aTy of
        TApp (TApp With _) y -> pure y
        _ -> throwError $ _ExpectedWith # aTy
    App f x -> do
      fTy <- infer f
      case fTy of
        TApp (TApp Arrow a) b -> b <$ check x a
        _ -> throwError $ _ExpectedArrow # fTy
    Ctor{} -> throwError $ _Can'tInfer # c
    Ann a b -> b <$ check a b

checkIndDecl ::
  ( AsScopeError e, AsKindError e, MonadError e m
  , MonadReader TCEnv m
  ) =>
  IndDecl ->
  m ()
checkIndDecl decl = do
  unless (k == KVType) . throwError $ _KindMismatch # (KVType, k)
  for_ (_indCtors decl) $ \ctor ->
    locally envKinds (params <>) $
    for_ (_indCtorArgs ctor) $ \argTy -> checkKind argTy KVType
  where
    (params, k) = unfoldKArr (_indTypeKind decl)

data TCError
  = TCScopeError ScopeError
  | TCTypeError TypeError
  | TCKindError KindError
  deriving Show
makePrisms ''TCError

instance AsScopeError TCError where; _ScopeError = _TCScopeError
instance AsTypeError TCError where; _TypeError = _TCTypeError
instance AsKindError TCError where; _KindError = _TCKindError

tc ::
  ( forall m e
  . ( AsScopeError e, AsTypeError e, AsKindError e, MonadError e m
    , MonadReader TCEnv m
    ) =>
    m a
  ) ->
  TCEnv -> Either TCError a
tc m e = runExcept (runReaderT m e)

sumDecl :: IndDecl
sumDecl =
  IndDecl
  { _indTypeName = "Sum"
  , _indTypeKind = KArr KVType $ KArr KVType KVType
  , _indCtors =
    [ IndCtor
      { _indCtorName = "inl"
      , _indCtorArity = 1
      , _indCtorArgs = [TVar 0]
      }
    , IndCtor
      { _indCtorName = "inr"
      , _indCtorArity = 1
      , _indCtorArgs = [TVar 1]
      }
    ]
  }

unitDecl :: IndDecl
unitDecl =
  IndDecl
  { _indTypeName = "Unit"
  , _indTypeKind = KVType
  , _indCtors =
    [ IndCtor
      { _indCtorName = "unit"
      , _indCtorArity = 0
      , _indCtorArgs = []
      }
    ]
  }