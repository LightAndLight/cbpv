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
    ExpectedF tyNames a ->
      tmismatch (Pretty.text "F ?") (prettyTy tyNames a)
    ExpectedU tyNames a ->
      tmismatch (Pretty.text "U ?") (prettyTy tyNames a)
    ExpectedArrow tyNames a ->
      tmismatch (Pretty.text "? -> ?") (prettyTy tyNames a)
    ExpectedInductive tyNames a ->
      Pretty.hsep [prettyTy tyNames a, Pretty.text "is not an inductive type"]
    ExpectedCoinductive tyNames a ->
      Pretty.hsep [prettyTy tyNames a, Pretty.text "is not a coinductive type"]
    ExpectedForall tyNames a ->
      tmismatch (Pretty.text "forall (? : ?). ?") (prettyTy tyNames a)
    TypeMismatch tyNames a b ->
      tmismatch (prettyTy tyNames a) (prettyTy tyNames b)
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
  = ExpectedKArr (Int -> Maybe Doc) Ty Kind
  | KindMismatch (Int -> Maybe Doc) Ty Kind Kind
  | TypeNotInScope (Int -> Maybe Doc) Int
  | InductiveShouldBeVal Text Kind
  | CoinductiveShouldBeComp Text Kind
makeClassyPrisms ''KindError

prettyKindError :: KindError -> Doc
prettyKindError ke =
  case ke of
    ExpectedKArr tyNames ty a ->
      Pretty.hsep
      [ Pretty.text "Kind mismatch: Type"
      , Pretty.squotes $ prettyTy tyNames ty
      , Pretty.text "should have kind '? -> ?', but it has kind"
      , Pretty.squotes $ prettyKind a
      ]
    KindMismatch tyNames ty a b ->
      Pretty.hsep
      [ Pretty.text "Kind mismatch: Type"
      , Pretty.squotes $ prettyTy tyNames ty
      , Pretty.text "should have kind"
      , Pretty.squotes $ prettyKind a
      , Pretty.text "but it has kind"
      , Pretty.squotes $ prettyKind b
      ]
    TypeNotInScope tyNames n ->
      fromMaybe (Pretty.char '#' <> Pretty.int n) (tyNames n) <>
      Pretty.text " not in scope"
    InductiveShouldBeVal n k ->
      Pretty.hsep
      [ Pretty.text "Inductive type"
      , Pretty.squotes . Pretty.text $ Text.unpack n
      , Pretty.text "should have kind 'Val'"
      , Pretty.text "but it has kind"
      , Pretty.squotes $ prettyKind k
      ]
    CoinductiveShouldBeComp n k ->
      Pretty.hsep
      [ Pretty.text "Coinductive type"
      , Pretty.squotes . Pretty.text $ Text.unpack n
      , Pretty.text "should have kind 'Comp'"
      , Pretty.text "but it has kind"
      , Pretty.squotes $ prettyKind k
      ]

ix :: Int -> [a] -> Maybe a
ix _ [] = Nothing
ix 0 (x:_) = Just x
ix n (_:xs) = ix (n-1) xs

namesDoc :: (Int -> Maybe Text) -> Int -> Maybe Doc
namesDoc f = fmap (Pretty.text . Text.unpack) . f

data TCEnv
  = TCEnv
  { _envVarNames :: Int -> Maybe Text
  , _envTypes :: [Ty]
  , _envTyNames :: Int -> Maybe Text
  , _envKinds :: [Kind]
  , _envDecls :: Map Text (Exp 'V, Ty)
  , _envIndDecls :: [IndDecl]
  , _envCoIndDecls :: [CoIndDecl]
  }
makeLenses ''TCEnv

emptyTCEnv :: TCEnv
emptyTCEnv =
  TCEnv
  { _envVarNames = const Nothing
  , _envTypes = mempty
  , _envTyNames = const Nothing
  , _envKinds = mempty
  , _envDecls = mempty
  , _envIndDecls = mempty
  , _envCoIndDecls = mempty
  }

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
    TForall name k a ->
      locally envKinds (k :) .
      locally envTyNames (\f -> \case; 0 -> name; n -> f (n-1)) $
      inferKind a
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
        Nothing -> do
          tyNames <- asks (namesDoc . _envTyNames)
          throwError $ _TypeNotInScope # (tyNames, n)
        Just k -> pure k
    TApp a b -> do
      aKind <- inferKind a
      case aKind of
        KArr x y -> y <$ checkKind b x
        _ -> do
          tyNames <- asks (namesDoc . _envTyNames)
          throwError $ _ExpectedKArr # (tyNames, a, aKind)

checkKind ::
  (AsScopeError e, AsKindError e, MonadError e m, MonadReader TCEnv m) =>
  Ty -> Kind -> m ()
checkKind ty k = do
  k' <- inferKind ty
  unless (k == k') $ do
    tyNames <- asks (namesDoc . _envTyNames)
    throwError $ _KindMismatch # (tyNames, ty, k, k')

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
    _ -> do
      varNames <- asks (namesDoc . _envVarNames)
      throwError $ _ExpectedInductive # (varNames, ty)

check ::
  (AsScopeError e, AsKindError e, AsTypeError e, MonadError e m, MonadReader TCEnv m) =>
  Exp a -> Ty -> m ()
check a ty =
  case a of
    Ctor n as -> checkCtor n as ty
    _ -> do
      aTy <- infer a
      tyNames <- asks (namesDoc . _envTyNames)
      unless (aTy == ty) . throwError $ _TypeMismatch # (tyNames, ty, aTy)

checkPattern ::
  (AsScopeError e, AsKindError e, AsTypeError e, MonadError e m, MonadReader TCEnv m) =>
  Pattern -> Ty -> m ([Maybe Text], [Ty])
checkPattern PWild _ = pure ([], [])
checkPattern (PVar n) ty = pure ([n], [ty])
checkPattern (PCtor n act ns) ty =
  case unfoldTApp ty of
    (TCtor nty, targs) -> do
      decl <- lookupIndDecl nty
      ctor <- lookupIndCtor n $ _indCtors decl
      let ex = _indCtorArity ctor
      unless (ex == act) . throwError $ _CtorExpectedArity # (ex, act)
      pure (ns, substTy (targs !!) <$> _indCtorArgs ctor)
    _ -> do
      tyNames <- asks (namesDoc . _envTyNames)
      throwError $ _ExpectedInductive # (tyNames, ty)

infer ::
  (AsScopeError e, AsTypeError e, AsKindError e, MonadError e m, MonadReader TCEnv m) =>
  Exp a -> m Ty
infer c =
  case c of
    Addr{} -> error "Addr"
    AppTy a t -> do
      aTy <- infer a
      case aTy of
        TForall _ k rest -> rest <$ checkKind t k
        _ -> do
          tyNames <- asks (namesDoc . _envTyNames)
          throwError $ _ExpectedForall # (tyNames, aTy)
    AbsTy name k a ->
      fmap (TForall name k) .
      locally envKinds (k :) .
      locally envTyNames (\f -> \case; 0 -> name; n -> f (n-1)) $
      infer a
    Name n -> do
      (_, ty) <- lookupDecl n
      pure ty
    Var n -> do
      ctx <- asks _envTypes
      case ix n ctx of
        Nothing -> do
          varNames <- asks (namesDoc . _envVarNames)
          throwError $ _VarNotInScope # (varNames, n)
        Just t -> pure t
    Thunk a -> TApp U <$> infer a
    Return a -> TApp F <$> infer a
    Abs name ty a -> do
      checkKind ty KVal
      fmap (TApp (TApp Arrow ty)) .
        locally envTypes (ty :) .
        locally envVarNames (\f -> \case; 0 -> name; n -> f (n-1)) $
        infer a
    Bind name a b -> do
      aTy <- infer a
      case aTy of
        TApp F i ->
          locally envTypes (i :) .
          locally envVarNames (\f -> \case; 0 -> name; n -> f (n-1)) $
          infer b
        _ -> do
          tyNames <- asks (namesDoc . _envTyNames)
          throwError $ _ExpectedF # (tyNames, aTy)
    Let name a b -> do
      aTy <- infer a
      locally envTypes (aTy :) .
        locally envVarNames (\f -> \case; 0 -> name; n -> f (n-1)) $
        infer b
    Fix name t a ->
      case t of
        TApp U t' -> do
          aTy <-
            locally envTypes (t :) .
            locally envVarNames (\f -> \case; 0 -> name; n -> f (n-1)) $
            infer a
          unless (aTy == t') $ do
            tyNames <- asks (namesDoc . _envTyNames)
            throwError $ _TypeMismatch # (tyNames, t', aTy)
          pure aTy
        _ -> do
          tyNames <- asks (namesDoc . _envTyNames)
          throwError $ _ExpectedU # (tyNames, t)
    Force a -> do
      aTy <- infer a
      case aTy of
        TApp U i -> pure i
        _ -> do
          tyNames <- asks (namesDoc . _envTyNames)
          throwError $ _ExpectedU # (tyNames, aTy)
    Case a bs -> do
      aTy <- infer a
      ts <- for bs $ \(Branch p b) -> do
        (ns, vs) <- checkPattern p aTy
        let arity = patArity p
        locally envTypes (vs <>) .
          locally envVarNames (\f n -> if n < arity then ns !! n else f (n-arity)) $
          infer b
      foldlM1
        (\x y -> do
           unless (x == y) $ do
             tyNames <- asks (namesDoc . _envTyNames)
             throwError $ _TypeMismatch # (tyNames, x, y)
           pure x)
        ts
    CoCase t bs -> do
      checkKind t KComp
      let (tc, targs) = unfoldTApp t
      case tc of
        TCtor name -> do
          decl <- lookupCoIndDecl name
          for_ bs $ \(CoBranch d arity tys names e) -> do
            dtor <- lookupCoIndDtor d $ _coIndDtors decl
            locally envTypes (tys ++) .
              locally envVarNames (\f n -> if n < arity then Just (names !! n) else f (n-arity)) .
              check e $ substTy (targs !!) (_coIndDtorType dtor)
          pure t
        _ -> do
          tyNames <- asks (namesDoc . _envTyNames)
          throwError $ _ExpectedCoinductive # (tyNames, tc)
    Dtor n bs a -> do
      (decl, dtor) <- findCoIndDtor n
      aTy <- infer a
      let
        (tc, targs) = unfoldTApp aTy
        ety = TCtor (_coIndTypeName decl)
      unless (tc == ety) $ do
        tyNames <- asks (namesDoc . _envTyNames)
        throwError $ _TypeMismatch # (tyNames, ety, tc)
      for_ (zip bs $ _coIndDtorArgs dtor) (uncurry check)
      let retTy = substTy (targs !!) (_coIndDtorType dtor)
      retTy <$ checkKind retTy KComp
    App f x -> do
      fTy <- infer f
      case fTy of
        TApp (TApp Arrow a) b -> b <$ check x a
        _ -> do
          tyNames <- asks (namesDoc . _envTyNames)
          throwError $ _ExpectedArrow # (tyNames, fTy)
    Ctor{} -> do
      varNames <- asks (namesDoc . _envVarNames)
      tyNames <- asks (namesDoc . _envTyNames)
      throwError $ _Can'tInfer # (varNames, tyNames, c)
    Ann a b -> b <$ check a b

checkIndDecl ::
  ( AsScopeError e, AsKindError e, MonadError e m
  , MonadReader TCEnv m
  ) =>
  IndDecl -> m ()
checkIndDecl decl = do
  unless (k == KVal) . throwError $
    _InductiveShouldBeVal # (_indTypeName decl, k)
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
    _CoinductiveShouldBeComp # (_coIndTypeName decl, k)
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
  (n, e, ty) <$ checkKind ty KVal

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
  | TCompError TypeError
  | TCKindError KindError
makePrisms ''TCError

prettyTCError :: TCError -> Doc
prettyTCError (TCKindError a) = prettyKindError a
prettyTCError (TCompError a) = prettyTypeError a
prettyTCError (TCScopeError a) = prettyScopeError a

instance AsScopeError TCError where; _ScopeError = _TCScopeError
instance AsTypeError TCError where; _TypeError = _TCompError
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
      , _coIndDtorArity = 0
      , _coIndDtorArgs = []
      , _coIndDtorType = TVar 0
      }
    , CoIndDtor
      { _coIndDtorName = "tail"
      , _coIndDtorArity = 0
      , _coIndDtorArgs = []
      , _coIndDtorType = TApp (TCtor "Stream") (TVar 0)
      }
    ]
  }