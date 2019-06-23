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
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Semigroup.Foldable (foldlM1)
import Data.Text (Text)
import Data.Traversable (for)
import Text.PrettyPrint.ANSI.Leijen (Doc)

import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

import Syntax
import Printer

data ScopeError
  = InductiveNotInScope Text
  | CoinductiveNotInScope Text
  | TyCtorNotInScope Text
  | AmbiguousTyCtor Text
  | CtorNotInScope Text
  | DtorNotInScope Text
  | VarNotInScope (Int -> Maybe Doc) Int
  | UnboundName Text

prettyScopeError :: ScopeError -> Doc
prettyScopeError se =
  case se of
    InductiveNotInScope a ->
      Pretty.text "Inductive type '" <>
      Pretty.text (Text.unpack a) <>
      Pretty.text "' not in scope"
    CoinductiveNotInScope a ->
      Pretty.text "Coinductive type '" <>
      Pretty.text (Text.unpack a) <>
      Pretty.text "' not in scope"
    TyCtorNotInScope a ->
      Pretty.text "Type constructor '" <>
      Pretty.text (Text.unpack a) <>
      Pretty.text "' not in scope"
    AmbiguousTyCtor a ->
      Pretty.text "Ambiguous type constructor '" <>
      Pretty.text (Text.unpack a) <>
      Pretty.text "' - there is both an inductive and a coinductive type with that name"
    CtorNotInScope a ->
      Pretty.text "Constructor '" <>
      Pretty.text (Text.unpack a) <>
      Pretty.text "' not in scope"
    DtorNotInScope a ->
      Pretty.text "Destructor '" <>
      Pretty.text (Text.unpack a) <>
      Pretty.text "' not in scope"
    VarNotInScope exNames a ->
      Pretty.text "Variable '" <>
      fromMaybe (Pretty.char '#' <> Pretty.int a) (exNames a) <>
      Pretty.text "' not in scope"
    UnboundName a ->
      Pretty.text "Unbound name '" <>
      Pretty.text (Text.unpack a) <>
      Pretty.char '\''

data TypeError
  = ExpectedF (Int -> Maybe Doc) Ty
  | ExpectedU (Int -> Maybe Doc) Ty
  | ExpectedArrow (Int -> Maybe Doc) Ty
  | ExpectedInductive (Int -> Maybe Doc) Ty
  | ExpectedCoinductive (Int -> Maybe Doc) Ty
  | ExpectedForall (Int -> Maybe Doc) Ty
  | TypeMismatch (Int -> Maybe Doc) Ty Ty
  | CtorExpectedArity Int Int
  | Can'tInfer (Int -> Maybe Doc) (Int -> Maybe Doc) (Exp 'V)

prettyTypeError :: TypeError -> Doc
prettyTypeError te =
  case te of
    ExpectedF tyNames a -> tmismatch (Pretty.text "F ?") (prettyTy tyNames a)
    ExpectedU tyNames a -> tmismatch (Pretty.text "U ?") (prettyTy tyNames a)
    ExpectedArrow tyNames a -> tmismatch (Pretty.text "? -> ?") (prettyTy tyNames a)
    ExpectedInductive tyNames a -> Pretty.hsep [prettyTy tyNames a, Pretty.text "is not an inductive type"]
    ExpectedCoinductive tyNames a -> Pretty.hsep [prettyTy tyNames a, Pretty.text "is not a coinductive type"]
    ExpectedForall tyNames a -> tmismatch (Pretty.text "forall (? : ?). ?") (prettyTy tyNames a)
    TypeMismatch tyNames a b -> tmismatch (prettyTy tyNames a) (prettyTy tyNames b)
    CtorExpectedArity a b ->
      Pretty.hsep
      [ Pretty.text "Incorrect number of arguments to constructor: Expected"
      , Pretty.int a
      , Pretty.text "but got"
      , Pretty.int b
      ]
    Can'tInfer exNames tyNames a ->
      Pretty.hsep
      [ Pretty.text "Can't infer type for"
      , prettyExp exNames tyNames a
      ]
  where
    tmismatch t1 t2 =
      Pretty.hsep
      [ Pretty.text "Type mismatch: Expected '" <> t1 <> Pretty.text "', but got"
      , t2 <> Pretty.char '\''
      ]

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

lookupCoIndDtor ::
  (AsScopeError e, MonadError e m) =>
  Text -> [CoIndDtor] -> m CoIndDtor
lookupCoIndDtor a cs =
  maybe (throwError $ _CtorNotInScope # a) pure $ go cs
  where
    go [] = Nothing
    go (i : is) =
      if _coIndDtorName i == a
      then Just i
      else go is

lookupCoIndDecl ::
  (HasCoIndDecls r, MonadReader r m, AsScopeError e, MonadError e m) =>
  Text -> m CoIndDecl
lookupCoIndDecl a =
  go <$> view coIndDecls >>=
  maybe (throwError $ _CoinductiveNotInScope # a) pure
  where
    go [] = Nothing
    go (i : is) =
      if _coIndTypeName i == a
      then Just i
      else go is

findCoIndDtor ::
  (HasCoIndDecls r, MonadReader r m, AsScopeError e, MonadError e m) =>
  Text -> m (CoIndDecl, CoIndDtor)
findCoIndDtor a = view coIndDecls >>= go
  where
    go [] = throwError $ _DtorNotInScope # a
    go (t : ts) =
      catchError
        ((,) t <$> lookupCoIndDtor a (_coIndDtors t))
        (\_ -> go ts)

data KindError
  = ExpectedCType Kind
  | ExpectedVType Kind
  | ExpectedKArr Kind
  | KindMismatch Kind Kind
  | TypeNotInScope (Int -> Maybe Doc) Int
makeClassyPrisms ''KindError

prettyKindError :: KindError -> Doc
prettyKindError ke =
  case ke of
    ExpectedCType a ->
      Pretty.hsep
      [ Pretty.text "Kind mismatch: Expected Comp, but got"
      , prettyKind a
      ]
    ExpectedVType a ->
      Pretty.hsep
      [ Pretty.text "Kind mismatch: Expected Val, but got"
      , prettyKind a
      ]
    ExpectedKArr a ->
      Pretty.hsep
      [ Pretty.text "Kind mismatch: Expected ? -> ?, but got"
      , prettyKind a
      ]
    KindMismatch a b ->
      Pretty.hsep
      [ Pretty.text "Kind mismatch: Expected"
      , prettyKind a <> Pretty.comma
      , Pretty.text "but got"
      , prettyKind b
      ]
    TypeNotInScope tyNames n ->
      fromMaybe (Pretty.char '#' <> Pretty.int n) (tyNames n) <>
      Pretty.text " not in scope"

ix :: Int -> [a] -> Maybe a
ix _ [] = Nothing
ix 0 (x:_) = Just x
ix n (_:xs) = ix (n-1) xs

data TCEnv
  = TCEnv
  { _envTypes :: [Ty]
  , _envKinds :: [Kind]
  , _envDecls :: Map Text (Exp 'V, Ty)
  , _envIndDecls :: [IndDecl]
  , _envCoIndDecls :: [CoIndDecl]
  }
makeLenses ''TCEnv

emptyTCEnv :: TCEnv
emptyTCEnv = TCEnv mempty mempty mempty mempty mempty

lookupDecl :: (MonadReader TCEnv m, AsScopeError e, MonadError e m) => Text -> m (Exp 'V, Ty)
lookupDecl n = do
  res <- asks $ Map.lookup n . _envDecls
  case res of
    Nothing -> throwError $ _UnboundName # n
    Just a -> pure a

instance HasIndDecls TCEnv where; indDecls = envIndDecls
instance HasCoIndDecls TCEnv where; coIndDecls = envCoIndDecls

inferKind ::
  (AsScopeError e, AsKindError e, MonadError e m, MonadReader TCEnv m) =>
  Ty -> m Kind
inferKind ty =
  case ty of
    TName a -> throwError $ _UnboundName # a
    TForall _ k a -> locally envKinds (k :) $ inferKind a
    U -> pure $ KArr KComp KVal
    TCtor n -> do
      mind <-
        catchError (Just <$> lookupIndDecl n) $ \_ -> pure Nothing
      mcoind <-
        catchError (Just <$> lookupCoIndDecl n) $ \_ -> pure Nothing
      case (mind, mcoind) of
        (Nothing, Nothing) -> throwError $ _TyCtorNotInScope # n
        (Just decl, Nothing) -> pure $ _indTypeKind decl
        (Nothing, Just decl) -> pure $ _coIndTypeKind decl
        (Just{}, Just{}) -> throwError $ _AmbiguousTyCtor # n
    F -> pure $ KArr KVal KComp
    Arrow -> pure $ KArr KVal (KArr KComp KComp)
    TVar n -> do
      kctx <- asks _envKinds
      case ix n kctx of
        Nothing -> throwError $ _TypeNotInScope # (_, n)
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
    (TCtor tname, targs) -> do
      decl <- lookupIndDecl tname
      ctor <- lookupIndCtor name (_indCtors decl)
      let
        actualArity = length args
        expectedArity = _indCtorArity ctor
      unless (expectedArity == actualArity) . throwError $
        _CtorExpectedArity # (expectedArity, actualArity)
      let instTys = substTy (targs !!) <$> _indCtorArgs ctor
      traverse_ (uncurry check) (zip args instTys)
    _ -> throwError $ _ExpectedInductive # (_, ty)

check ::
  (AsScopeError e, AsKindError e, AsTypeError e, MonadError e m, MonadReader TCEnv m) =>
  Exp a -> Ty -> m ()
check a ty =
  case a of
    Ctor n as -> checkCtor n as ty
    _ -> do
      aTy <- infer a
      unless (aTy == ty) . throwError $ _TypeMismatch # (_, ty, aTy)

checkPattern ::
  (AsScopeError e, AsKindError e, AsTypeError e, MonadError e m, MonadReader TCEnv m) =>
  Pattern -> Ty -> m [Ty]
checkPattern PWild _ = pure []
checkPattern (PVar _) ty = pure [ty]
checkPattern (PCtor n act _) ty =
  case unfoldTApp ty of
    (TCtor nty, targs) -> do
      decl <- lookupIndDecl nty
      ctor <- lookupIndCtor n $ _indCtors decl
      let ex = _indCtorArity ctor
      unless (ex == act) . throwError $ _CtorExpectedArity # (ex, act)
      pure $ substTy (targs !!) <$> _indCtorArgs ctor
    _ -> throwError $ _ExpectedInductive # (_, ty)

infer ::
  (AsScopeError e, AsTypeError e, AsKindError e, MonadError e m, MonadReader TCEnv m) =>
  Exp a -> m Ty
infer c =
  case c of
    AppTy a t -> do
      aTy <- infer a
      case aTy of
        TForall _ k rest -> rest <$ checkKind t k
        _ -> throwError $ _ExpectedForall # (_, aTy)
    AbsTy n k a ->
      TForall n k  <$> locally envKinds (k :) (infer a)
    Name n -> do
      (_, ty) <- lookupDecl n
      pure ty
    Var n -> do
      ctx <- asks _envTypes
      case ix n ctx of
        Nothing -> throwError $ _VarNotInScope # (_, n)
        Just t -> pure t
    Thunk a -> TApp U <$> infer a
    Return a -> TApp F <$> infer a
    Abs _ ty a -> do
      checkKind ty KVal
      TApp (TApp Arrow ty) <$> locally envTypes (ty :) (infer a)
    Bind _ a b -> do
      aTy <- infer a
      case aTy of
        TApp F i -> locally envTypes (i :) $ infer b
        _ -> throwError $ _ExpectedF # (_, aTy)
    Let _ a b -> do
      aTy <- infer a
      locally envTypes (aTy :) $ infer b
    Fix _ t a ->
      case t of
        TApp U t' -> do
          aTy <- locally envTypes (t :) $ infer a
          unless (aTy == t') . throwError $ _TypeMismatch # (_, t', aTy)
          pure aTy
        _ -> throwError $ _ExpectedU # (_, t)
    Force a -> do
      aTy <- infer a
      case aTy of
        TApp U i -> pure i
        _ -> throwError $ _ExpectedU # (_, aTy)
    Case a bs -> do
      aTy <- infer a
      ts <- for bs $ \(Branch p b) -> do
        vs <- checkPattern p aTy
        locally envTypes (vs <>) $ infer b
      foldlM1
        (\x y -> do
           unless (x == y) . throwError $ _TypeMismatch # (_, x, y)
           pure x)
        ts
    CoCase t bs -> do
      checkKind t KComp
      let (tc, targs) = unfoldTApp t
      case tc of
        TCtor n -> do
          decl <- lookupCoIndDecl n
          for_ bs $ \(CoBranch d e) -> do
            dtor <- lookupCoIndDtor d $ _coIndDtors decl
            check e $ substTy (targs !!) (_coIndDtorType dtor)
          pure t
        _ -> throwError $ _ExpectedCoinductive # (_, tc)
    Dtor n a -> do
      (decl, dtor) <- findCoIndDtor n
      aTy <- infer a
      let
        (tc, targs) = unfoldTApp aTy
        ety = TCtor (_coIndTypeName decl)
      unless (tc == ety) . throwError $ _TypeMismatch # (_, ety, tc)
      let retTy = substTy (targs !!) (_coIndDtorType dtor)
      checkKind retTy KComp
      pure retTy
    App f x -> do
      fTy <- infer f
      case fTy of
        TApp (TApp Arrow a) b -> b <$ check x a
        _ -> throwError $ _ExpectedArrow # (_, fTy)
    Ctor{} -> throwError $ _Can'tInfer # (_, _, c)
    Ann a b -> b <$ check a b

checkIndDecl ::
  ( AsScopeError e, AsKindError e, MonadError e m
  , MonadReader TCEnv m
  ) =>
  IndDecl -> m ()
checkIndDecl decl = do
  unless (k == KVal) . throwError $ _KindMismatch # (KVal, k)
  for_ (_indCtors decl) $ \ctor ->
    locally envKinds (params <>) $
    for_ (_indCtorArgs ctor) $ \argTy ->
      locally envIndDecls (decl :) $ checkKind argTy KVal
  where
    (params, k) = unfoldKArr (_indTypeKind decl)

checkCoIndDecl ::
  ( AsScopeError e, AsKindError e, MonadError e m
  , MonadReader TCEnv m
  ) =>
  CoIndDecl -> m ()
checkCoIndDecl decl = do
  unless (k == KComp) . throwError $
    _KindMismatch # (KComp, k)
  for_ (_coIndDtors decl) $ \dtor ->
    locally envKinds (params <>) .
    locally envCoIndDecls (decl :) $
    checkKind (_coIndDtorType dtor) KComp
  where
    (params, k) = unfoldKArr (_coIndTypeKind decl)

checkDecl ::
  ( MonadReader TCEnv m
  , AsScopeError e, AsTypeError e, AsKindError e, MonadError e m
  ) =>
  Decl -> m (Text, Exp 'V, Ty)
checkDecl (Decl n e) = do
  ty <- infer e
  pure (n, e, ty)

checkModule ::
  ( MonadReader TCEnv m
  , AsScopeError e, AsTypeError e, AsKindError e, MonadError e m
  ) =>
  Module ->
  m ()
checkModule MEmpty = pure ()
checkModule (MDecl d rest) = do
  (n, e, ty) <- checkDecl d
  locally envDecls (Map.insert n (e, ty)) $ checkModule rest
checkModule (MIndDecl d rest) = do
  checkIndDecl d
  locally envIndDecls (d :) $ checkModule rest
checkModule (MCoIndDecl d rest) = do
  checkCoIndDecl d
  locally envCoIndDecls (d :) $ checkModule rest

data TCError
  = TCScopeError ScopeError
  | TCTypeError TypeError
  | TCKindError KindError
makePrisms ''TCError

prettyTCError :: TCError -> Doc
prettyTCError (TCKindError a) = prettyKindError a
prettyTCError (TCTypeError a) = prettyTypeError a
prettyTCError (TCScopeError a) = prettyScopeError a

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
  , _indTypeParams = ["a", "b"]
  , _indTypeKind = KArr KVal $ KArr KVal KVal
  , _indCtors =
    [ IndCtor
      { _indCtorName = "Left"
      , _indCtorArity = 1
      , _indCtorArgs = [TVar 0]
      }
    , IndCtor
      { _indCtorName = "Right"
      , _indCtorArity = 1
      , _indCtorArgs = [TVar 1]
      }
    ]
  }

natDecl :: IndDecl
natDecl =
  IndDecl
  { _indTypeName = "Nat"
  , _indTypeParams = []
  , _indTypeKind = KVal
  , _indCtors =
    [ IndCtor
      { _indCtorName = "Z"
      , _indCtorArity = 0
      , _indCtorArgs = []
      }
    , IndCtor
      { _indCtorName = "S"
      , _indCtorArity = 1
      , _indCtorArgs = [TCtor "Nat"]
      }
    ]
  }

unitDecl :: IndDecl
unitDecl =
  IndDecl
  { _indTypeName = "Unit"
  , _indTypeParams = []
  , _indTypeKind = KVal
  , _indCtors =
    [ IndCtor
      { _indCtorName = "Unit"
      , _indCtorArity = 0
      , _indCtorArgs = []
      }
    ]
  }

streamDecl :: CoIndDecl
streamDecl =
  CoIndDecl
  { _coIndTypeName = "Stream"
  , _coIndTypeParams = ["a"]
  , _coIndTypeKind = KArr KComp KComp
  , _coIndDtors =
    [ CoIndDtor
      { _coIndDtorName = "head"
      , _coIndDtorType = TVar 0
      }
    , CoIndDtor
      { _coIndDtorName = "tail"
      , _coIndDtorType = TApp (TCtor "Stream") (TVar 0)
      }
    ]
  }