{-# language DataKinds, GADTs #-}
{-# language BangPatterns #-}
{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language TemplateHaskell #-}
module Typecheck where

import Control.Lens.Getter (view)
import Control.Lens.Review ((#))
import Control.Lens.Setter (locally)
import Control.Lens.TH (makeClassyPrisms, makeLenses, makePrisms)
import Control.Monad (unless)
import Control.Monad.Except
  (MonadError, runExcept, throwError, catchError)
import Control.Monad.Reader (MonadReader, runReaderT, asks)
import Data.Foldable (traverse_, for_)
import Data.Semigroup.Foldable (foldlM1)
import Data.Text (Text)
import Data.Traversable (for)

import Syntax

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