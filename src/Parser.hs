{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language TypeFamilies #-}
module Parser where

import Control.Applicative (Alternative, (<|>), many, some, optional)
import Control.Lens.Setter (over, mapped)
import Data.ByteString (ByteString)
import Data.Char (isSpace)
import Data.List.NonEmpty (NonEmpty(..))
import Data.String (fromString)
import Data.Text (Text)
import Text.Parser.Combinators (Parsing, (<?>), eof, sepBy, sepBy1, skipMany)
import Text.Parser.Char (CharParsing, alphaNum, lower, upper, newline, satisfy)
import Text.Parser.Token (TokenParsing, IdentifierStyle(..), Unlined(..))
import Text.Trifecta.Delta (Delta(..))
import Text.Trifecta.Parser (runParser)
import Text.Trifecta.Result (Result)

import qualified Text.Parser.Token as Token
import qualified Text.Parser.Token.Highlight as Highlight

import Syntax

newtype Nesting m a = Nesting { runNesting :: m a }
  deriving (Parsing, CharParsing, Functor, Applicative, Alternative, Monad)

instance TokenParsing m => TokenParsing (Nesting m) where
  someSpace = Nesting $ skipMany (satisfy isSpace)

identStyle :: CharParsing m => IdentifierStyle m
identStyle =
  IdentifierStyle
  { _styleName = "identifier"
  , _styleStart = lower
  , _styleLetter = alphaNum
  , _styleReserved =
    [ "force"
    , "return"
    , "thunk"
    , "let"
    , "fix"
    , "bind"
    , "in"
    , "forall"
    , "case"
    , "cocase"
    , "of"
    , "data"
    , "codata"
    , "where"
    ]
  , _styleHighlight = Highlight.Identifier
  , _styleReservedHighlight = Highlight.ReservedIdentifier
  }

ctorStyle :: CharParsing m => IdentifierStyle m
ctorStyle =
  IdentifierStyle
  { _styleName = "constructor"
  , _styleStart = upper
  , _styleLetter = alphaNum
  , _styleReserved = ["Val", "Comp"]
  , _styleHighlight = Highlight.Constructor
  , _styleReservedHighlight = Highlight.ReservedConstructor
  }

ctor :: (Monad m, TokenParsing m) => m Text
ctor = Token.ident ctorStyle

ident :: (Monad m, TokenParsing m) => m Text
ident = Token.ident identStyle

keyword :: (Monad m, TokenParsing m) => Text -> m ()
keyword = Token.reserveText identStyle

arrow :: TokenParsing m => m Text
arrow = Token.textSymbol "->"

val :: (Monad m, TokenParsing m) => m ()
val = Token.reserveText ctorStyle "Val"

comp :: (Monad m, TokenParsing m) => m ()
comp = Token.reserveText ctorStyle "Comp"

kind :: (Monad m, TokenParsing m) => m Kind
kind = foldr KArr <$> atom <*> many (arrow *> atom)
  where
    atom =
      KVal <$ val <|>
      KComp <$ comp <|>
      Token.parens kind

tyAtom :: (Monad m, TokenParsing m) => m Ty
tyAtom =
  (\case; "U" -> U; "F" -> F; c -> TCtor c) <$> ctor <|>
  TName <$> ident <|>
  Token.parens (Arrow <$ arrow <|> ty)

ty :: (Monad m, TokenParsing m) => m Ty
ty = (fa <|> arr) <?> "type"
  where
    fa =
      (\(a, b) -> TForall (Just a) b . abstractTy a) <$ keyword "forall" <*>
      Token.parens ((,) <$> ident <* Token.colon <*> kind) <* Token.dot <*>
      ty
    arr = (\a -> maybe a (TApp $ TApp Arrow a)) <$> app <*> optional (arrow *> arr)
    app = foldl TApp <$> tyAtom <*> many tyAtom

pattern_ :: (Monad m, TokenParsing m) => m (Pattern, [Text])
pattern_ =
  (PWild, []) <$ Token.symbolic '_' <|>
  (\a -> (PVar $ Just a, [a])) <$> ident <|>
  (\a bs -> (PCtor a (length bs) (Just <$> bs), bs)) <$>
    ctor <*>
    Token.brackets (ident `sepBy` Token.comma)

branch :: (Monad m, TokenParsing m) => m (Exp a) -> m (Branch a)
branch ex =
  (\(p, vs) e -> Branch p $ foldr abstract e vs) <$>
  pattern_ <* arrow <*>
  ex

cobranch :: (Monad m, TokenParsing m) => m CoBranch
cobranch =
  (\n as e ->
     let (ns, ts) = unzip as in
     CoBranch n (length as) ts ns $ foldr abstract e ns) <$>
  ident <*>
  Token.brackets
    (sepBy ((,) <$> ident <* Token.colon <*> ty) Token.comma) <* arrow <*>
  computation

braces :: TokenParsing m => Nesting m a -> m a
braces m = runNesting (Token.symbolic '{' *> m) <* Token.symbolic '}'

mkCase ::
  (Monad m, TokenParsing m) =>
  (forall n. (Monad n, TokenParsing n) => n (Exp a)) ->
  m (Exp a)
mkCase ex =
  Case <$ keyword "case" <*>
  value <* keyword "of" <*>
  braces ((:|) <$> branch ex <*> many (Token.semi *> branch ex))

mkLet ::
  (Monad m, TokenParsing m) =>
  m (Exp a) ->
  m (Exp a)
mkLet exbody =
  (\a b -> Let (Just a) b . abstract a) <$ keyword "let" <*>
  ident <* Token.symbolic '=' <*>
  value <* keyword "in" <*>
  exbody

mkAnn ::
  (Monad m, TokenParsing m) =>
  m (Exp a) ->
  m (Exp a)
mkAnn ex =
  (\a -> maybe a (Ann a)) <$> ex <*> optional (Token.colon *> ty)

computation :: (Monad m, TokenParsing m) => m (Exp 'C)
computation =
  (lam <|> ann <|> case_ <|> cocase <|> let_ <|> fix <|> bind) <?> "computation"
  where
    lam =
      either
        (\(a, b) -> Abs (Just a) b . abstract a)
        (\(a, b) -> AbsTy (Just a) b . abstractTyExp a) <$ Token.symbolic '\\' <*>
      (Left <$> Token.parens ((,) <$> ident <* Token.colon <*> ty) <|>
       Right <$ Token.symbolic '@' <*>
       Token.parens ((,) <$> ident <* Token.colon <*> kind)) <* arrow <*>
      computation

    let_ = mkLet computation

    bind =
      (\a b -> Bind (Just a) b . abstract a) <$ keyword "bind" <*>
      ident <* Token.symbolic '=' <*>
      computation <* keyword "in" <*>
      computation

    fix =
      (\n t -> Fix (Just n) t . abstract n) <$ keyword "fix" <*>
      ident <* Token.colon <*>
      ty <* keyword "in" <*>
      computation

    case_ = mkCase computation

    cocase =
      CoCase <$ keyword "cocase" <*>
      ty <* keyword "of" <*>
      braces ((:|) <$> cobranch <*> many (Token.semi *> cobranch))

    ann = mkAnn app

    app =
      foldl (\b -> either (App b) (AppTy b)) <$>
      dtor <*>
      many (Left <$> value <|> Right <$ Token.symbolic '@' <*> tyAtom)

    dtor =
      foldl (\a (b, c) -> Dtor b c a) <$>
      atom <*>
      many ((,) <$ Token.dot <*> ident <*> Token.brackets (sepBy value Token.comma))

    atom =
      Return <$ keyword "return" <*> Token.brackets value <|>
      Force <$ keyword "force" <*> Token.brackets value <|>
      Token.parens computation

value :: (Monad m, TokenParsing m) => m (Exp 'V)
value = (case_ <|> let_ <|> ann <|> absTy) <?> "value"
  where
    ann = mkAnn atom
    absTy =
      (\(a, b) -> AbsTy (Just a) b . abstractTyExp a) <$ Token.symbolic '\\' <* Token.symbolic '@' <*>
      Token.parens ((,) <$> ident <* Token.colon <*> kind) <* arrow <*>
      value
    let_ = mkLet value
    case_ = mkCase value
    atom =
      Thunk <$ keyword "thunk" <*> Token.brackets computation <|>
      Name <$> ident <|>
      Ctor <$> ctor <*> Token.brackets (sepBy value Token.comma) <|>
      Token.parens value

indDecl :: (Monad m, TokenParsing m) => m IndDecl
indDecl =
  (\n ps mctors ->
     let (pns, ks) = unzip ps in
     IndDecl n pns (foldr KArr KVal ks) $
     maybe [] (over (mapped.indCtorArgs.mapped) (abstractTys pns)) mctors) <$ keyword "data" <*>
  ctor <*>
  many (Token.parens $ (,) <$> ident <* Token.colon <*> kind) <*>
  optional
    (keyword "where" *> braces (sepBy1 ctorDecl Token.semi))
  where
    ctorDecl =
      (\n ps -> IndCtor n (length ps) ps) <$>
      ctor <*>
      Token.brackets (sepBy ty Token.comma)

coIndDecl :: (Monad m, TokenParsing m) => m CoIndDecl
coIndDecl =
  (\n ps mdtors ->
     let (pns, ks) = unzip ps in
     CoIndDecl n pns (foldr KArr KComp ks) $
     maybe [] (over (mapped.coIndDtorType) (abstractTys pns)) mdtors) <$ keyword "codata" <*>
  ctor <*>
  many (Token.parens $ (,) <$> ident <* Token.colon <*> kind) <*>
  optional
    (keyword "where" *> braces (sepBy1 dtorDecl Token.semi))
  where
    dtorDecl =
      (\n as -> CoIndDtor n (length as) as) <$>
      ident <*>
      Token.brackets (sepBy ty Token.comma) <* Token.colon <*>
      ty

decl :: (Monad m, TokenParsing m) => m Decl
decl =
  Decl <$>
  ident <* Token.symbolic '=' <*>
  (runNesting (Token.symbolic '{' *> value) <* Token.symbolic '}' <|>
   value)

module_ :: (Monad m, TokenParsing m) => m Module
module_ =
  runUnlined $
  foldr (either (either MDecl MIndDecl) MCoIndDecl) MEmpty <$>
  sepBy
    (Left . Left <$> decl <|>
     Left . Right <$> indDecl <|>
     Right <$> coIndDecl)
    (some $ newline <|> Token.whiteSpace *> newline)

parse ::
  String ->
  (forall m. (Monad m, TokenParsing m) => m a) ->
  ByteString -> Result a
parse s m = runParser (m <* eof) (Directed (fromString s) 0 0 0 0)
