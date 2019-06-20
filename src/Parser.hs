{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language TypeFamilies #-}
module Parser where

import Control.Applicative ((<|>), many, optional)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Text (Text)
import Data.Void (Void)
import Text.Megaparsec
  ((<?>), MonadParsec, Stream, satisfy, between, sepBy)

import qualified Text.Megaparsec as Parsec

import Lexer
import Syntax

newtype Tokens = Tokens { getTokens :: [Token] }
  deriving (Eq, Ord, Show)

instance Stream Tokens where
  type Token Tokens = Token
  type Tokens Tokens = [Token]

  tokensToChunk _ = id
  chunkToTokens _ = id
  chunkLength _ = length
  take1_ (Tokens ts) =
    case ts of
      [] -> Nothing
      x : xs -> Just (x, Tokens xs)
  takeN_ n (Tokens ts)
    | n <= 0 = Just ([], Tokens ts)
    | otherwise =
      case ts of
        [] -> Nothing
        _ -> let (a, b) = splitAt n ts in Just (a, Tokens b)
  takeWhile_ p (Tokens ts) = let (a, b) = span p ts in (a, Tokens b)
  showTokens _ (a :| as) = show (a:as)
  reachOffset = error "reachOffset: NIH"

tkSpace :: MonadParsec e Tokens m => m Token
tkSpace = satisfy (\case; TkSpace{} -> True; _ -> False)

tkNewline :: MonadParsec e Tokens m => m Token
tkNewline = satisfy (\case; TkNewline{} -> True; _ -> False)

space :: MonadParsec e Tokens m => Bool -> m Token
space True = tkSpace <|> tkNewline
space False = tkSpace

tkLParen :: MonadParsec e Tokens m => m Token
tkLParen = satisfy (\case; TkLParen{} -> True; _ -> False)

tkRParen :: MonadParsec e Tokens m => m Token
tkRParen = satisfy (\case; TkRParen{} -> True; _ -> False)

tkLBracket :: MonadParsec e Tokens m => m Token
tkLBracket = satisfy (\case; TkLBracket{} -> True; _ -> False)

tkRBracket :: MonadParsec e Tokens m => m Token
tkRBracket = satisfy (\case; TkRBracket{} -> True; _ -> False)

tkLBrace :: MonadParsec e Tokens m => m Token
tkLBrace = satisfy (\case; TkLBrace{} -> True; _ -> False)

tkRBrace :: MonadParsec e Tokens m => m Token
tkRBrace = satisfy (\case; TkRBrace{} -> True; _ -> False)

tkForall :: MonadParsec e Tokens m => m Token
tkForall = satisfy (\case; TkForall{} -> True; _ -> False)

tkColon :: MonadParsec e Tokens m => m Token
tkColon = satisfy (\case; TkColon{} -> True; _ -> False)

tkSemicolon :: MonadParsec e Tokens m => m Token
tkSemicolon = satisfy (\case; TkSemicolon{} -> True; _ -> False)

tkDot :: MonadParsec e Tokens m => m Token
tkDot = satisfy (\case; TkDot{} -> True; _ -> False)

tkAt :: MonadParsec e Tokens m => m Token
tkAt = satisfy (\case; TkDot{} -> True; _ -> False)

tkComma :: MonadParsec e Tokens m => m Token
tkComma = satisfy (\case; TkComma{} -> True; _ -> False)

tkArrow :: MonadParsec e Tokens m => m Token
tkArrow = satisfy (\case; TkArrow{} -> True; _ -> False)

tkVal :: MonadParsec e Tokens m => m Token
tkVal = satisfy (\case; TkVal{} -> True; _ -> False)

tkComp :: MonadParsec e Tokens m => m Token
tkComp = satisfy (\case; TkComp{} -> True; _ -> False)

tkThunk :: MonadParsec e Tokens m => m Token
tkThunk = satisfy (\case; TkThunk{} -> True; _ -> False)

tkReturn :: MonadParsec e Tokens m => m Token
tkReturn = satisfy (\case; TkReturn{} -> True; _ -> False)

tkForce :: MonadParsec e Tokens m => m Token
tkForce = satisfy (\case; TkForce{} -> True; _ -> False)

tkLet :: MonadParsec e Tokens m => m Token
tkLet = satisfy (\case; TkLet{} -> True; _ -> False)

tkFix :: MonadParsec e Tokens m => m Token
tkFix = satisfy (\case; TkFix{} -> True; _ -> False)

tkEquals :: MonadParsec e Tokens m => m Token
tkEquals = satisfy (\case; TkEquals{} -> True; _ -> False)

tkIn :: MonadParsec e Tokens m => m Token
tkIn = satisfy (\case; TkIn{} -> True; _ -> False)

tkCase :: MonadParsec e Tokens m => m Token
tkCase = satisfy (\case; TkCase{} -> True; _ -> False)

tkCoCase :: MonadParsec e Tokens m => m Token
tkCoCase = satisfy (\case; TkCoCase{} -> True; _ -> False)

tkOf :: MonadParsec e Tokens m => m Token
tkOf = satisfy (\case; TkOf{} -> True; _ -> False)

tkBackslash :: MonadParsec e Tokens m => m Token
tkBackslash = satisfy (\case; TkBackslash{} -> True; _ -> False)

tkUnderscore :: MonadParsec e Tokens m => m Token
tkUnderscore = satisfy (\case; TkUnderscore{} -> True; _ -> False)

tkIdent :: MonadParsec e Tokens m => m Text
tkIdent =
  (\case; TkIdent a _ -> a; _ -> undefined) <$>
  satisfy (\case; TkIdent{} -> True; _ -> False)

tkCtor :: MonadParsec e Tokens m => m Text
tkCtor =
  (\case; TkCtor a _ -> a; _ -> undefined) <$>
  satisfy (\case; TkCtor{} -> True; _ -> False)

parens :: MonadParsec e Tokens m => m a -> m a
parens = between tkLParen tkRParen

brackets :: MonadParsec e Tokens m => m a -> m a
brackets = between tkLBracket tkRBracket

braces :: MonadParsec e Tokens m => m a -> m a
braces = between tkLBrace tkRBrace

ctor :: MonadParsec e Tokens m => Text -> m Token
ctor t = satisfy (\case; TkCtor t' _ -> t == t'; _ -> False)

ident :: MonadParsec e Tokens m => Text -> m Token
ident t = satisfy (\case; TkIdent t' _ -> t == t'; _ -> False)

kind :: MonadParsec e Tokens m => m Kind
kind = foldr KArr <$> atom <*> many (tkArrow *> atom)
  where
    atom =
      KVal <$ tkVal <|>
      KComp <$ tkComp <|>
      parens kind

ty :: MonadParsec e Tokens m => m Ty
ty = (fa <|> arr) <?> "type"
  where
    fa =
      (\(a, b) -> TForall (Just a) b . abstractTy a) <$ tkForall <*>
      parens ((,) <$> tkIdent <* tkColon <*> kind) <* tkDot <*>
      ty
    arr = (\a -> maybe a (TApp $ TApp Arrow a)) <$> app <*> optional (tkArrow *> arr)
    app = foldl TApp <$> atom <*> many (space False *> atom)
    atom =
      U <$ ctor "U" <|>
      F <$ ctor "F" <|>
      TCtor <$> tkCtor <|>
      TName <$> tkIdent <|>
      parens (Arrow <$ tkArrow <|> ty)

pattern_ :: MonadParsec e Tokens m => m (Pattern, [Text])
pattern_ =
  (PWild, []) <$ tkUnderscore <|>
  (\a -> (PVar $ Just a, [a])) <$> tkIdent <|>
  (\a bs -> (PCtor a (length bs) bs, bs)) <$>
    tkCtor <*>
    brackets (tkIdent `sepBy` tkComma)

branch :: MonadParsec e Tokens m => (Bool -> m (Exp a)) -> m (Branch a)
branch ex =
  (\(p, vs) e -> Branch p $ foldr abstract e vs) <$>
  pattern_ <* tkArrow <*>
  ex True

cobranch :: MonadParsec e Tokens m => m CoBranch
cobranch =
  CoBranch <$>
  tkIdent <* tkArrow <*>
  computation True


mkCase ::
  MonadParsec e Tokens m =>
  Bool -> (Bool -> m (Exp a)) -> m (Exp a)
mkCase inBlock ex =
  Case <$ tkCase <*>
  value inBlock <* tkOf <*>
  braces
    ((:|) <$>
      branch ex <*>
      many (tkSemicolon *> branch ex))

mkLet ::
  MonadParsec e Tokens m =>
  Bool ->
  (Bool -> m (Exp a)) ->
  m (Exp a)
mkLet inBlock exbody =
  (\a b -> Let (Just a) b . abstract a) <$ tkLet <*>
  tkIdent <* tkEquals <*>
  value inBlock <* tkIn <*>
  exbody inBlock

computation :: MonadParsec e Tokens m => Bool -> m (Exp 'C)
computation inBlock =
  (lam <|> app <|> case_ <|> cocase <|> let_) <?> "computation"
  where
    lam =
      (\(a, b) -> Abs (Just a) b . abstract a) <$ tkBackslash <*>
      parens ((,) <$> tkIdent <* tkColon <*> ty) <* tkArrow <*>
      computation inBlock

    let_ = mkLet inBlock computation

    case_ = mkCase inBlock computation

    cocase =
      CoCase <$ tkCoCase <*>
      ty <* tkOf <*>
      braces ((:|) <$> cobranch <*> many (tkSemicolon *> cobranch))

    app =
      foldl (\b -> either (App b) (AppTy b)) <$>
      dtor <*>
      many
        (space inBlock *>
         (Left <$> value inBlock <|>
          Right <$ tkAt <*> ty))

    dtor =
      foldl (\a b -> Dtor b a) <$> atom <*> many (tkDot *> tkIdent)

    atom =
      Fix <$ tkFix <*> brackets (computation True) <|>
      Return <$ tkReturn <*> brackets (value True) <|>
      Force <$ tkForce <*> brackets (value True) <|>
      parens (computation True)

value :: MonadParsec e Tokens m => Bool -> m (Exp 'V)
value inBlock = (case_ <|> let_ <|> atom) <?> "value"
  where
    let_ = mkLet inBlock value
    case_ = mkCase inBlock value
    atom =
      Name <$> tkIdent <|>
      Thunk <$ tkThunk <*> brackets (computation True) <|>
      Ctor <$> tkCtor <*> brackets (sepBy (value True) tkComma) <|>
      parens (value inBlock)

parse ::
  String ->
  (forall m. MonadParsec Void Tokens m => m a) ->
  Tokens -> Either (Parsec.ParseErrorBundle Tokens Void) a
parse s m = Parsec.parse m s
