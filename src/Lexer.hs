{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language OverloadedStrings #-}
module Lexer where

import Prelude hiding (takeWhile)

import Control.Applicative ((<|>), optional)
import Data.Attoparsec.Text
import Data.Char (isAscii, isLower, isUpper)
import Data.Text (Text)

import qualified Data.Text as Text

data Token
  = TkForall Text Text
  | TkData Text Text
  | TkCodata Text Text
  | TkComma Text Text
  | TkUnderscore Text Text
  | TkNewline Text Text
  | TkSpace Text
  | TkBackslash Text Text
  | TkVal Text Text
  | TkComp Text Text
  | TkFix Text
  | TkLet Text Text
  | TkWhere Text Text
  | TkBind Text Text
  | TkIn Text Text
  | TkReturn Text
  | TkThunk Text
  | TkForce Text
  | TkIdent Text Text
  | TkCtor Text Text
  | TkPipe Text Text
  | TkDot Text Text
  | TkAt Text Text
  | TkLBrace Text Text
  | TkRBrace Text Text
  | TkLBracket Text Text
  | TkRBracket Text Text
  | TkLParen Text Text
  | TkRParen Text Text
  | TkEquals Text Text
  | TkArrow Text Text
  | TkCase Text Text
  | TkCoCase Text Text
  | TkOf Text Text
  | TkSemicolon Text Text
  | TkColon Text Text
  | TkEof Text
  deriving (Eq, Ord, Show)

append :: Token -> Text -> Maybe Token
append tk txt =
  case tk of
    TkData a b -> Just $ TkData a (b <> txt)
    TkCodata a b -> Just $ TkCodata a (b <> txt)
    TkNewline a b -> Just $ TkNewline a (b <> txt)
    TkComma a b -> Just $ TkComma a (b <> txt)
    TkUnderscore a b -> Just $ TkUnderscore a (b <> txt)
    TkBackslash a b -> Just $ TkBackslash a (b <> txt)
    TkForall a b -> Just $ TkForall a (b <> txt)
    TkVal a b -> Just $ TkVal a (b <> txt)
    TkComp a b -> Just $ TkComp a (b <> txt)
    TkSpace a -> Just $ TkSpace (a <> txt)
    TkFix{} -> Nothing
    TkLet a b -> Just $ TkLet a (b <> txt)
    TkWhere a b -> Just $ TkWhere a (b <> txt)
    TkBind a b -> Just $ TkBind a (b <> txt)
    TkIn a b -> Just $ TkIn a (b <> txt)
    TkReturn{} -> Nothing
    TkThunk{} -> Nothing
    TkForce{} -> Nothing
    TkIdent a b -> Just $ TkIdent a (b <> txt)
    TkCtor a b -> Just $ TkCtor a (b <> txt)
    TkPipe a b -> Just $ TkPipe a (b <> txt)
    TkDot a b -> Just $ TkDot a (b <> txt)
    TkAt a b -> Just $ TkAt a (b <> txt)
    TkLBrace a b -> Just $ TkLBrace a (b <> txt)
    TkRBrace a b -> Just $ TkRBrace a (b <> txt)
    TkLBracket a b -> Just $ TkLBracket a (b <> txt)
    TkRBracket a b -> Just $ TkRBracket a (b <> txt)
    TkLParen a b -> Just $ TkLParen a (b <> txt)
    TkRParen a b -> Just $ TkRParen a (b <> txt)
    TkEquals a b -> Just $ TkEquals a (b <> txt)
    TkArrow a b -> Just $ TkArrow a (b <> txt)
    TkCase a b -> Just $ TkCase a (b <> txt)
    TkCoCase a b -> Just $ TkCoCase a (b <> txt)
    TkOf a b -> Just $ TkOf a (b <> txt)
    TkSemicolon a b -> Just $ TkSemicolon a (b <> txt)
    TkColon a b -> Just $ TkColon a (b <> txt)
    TkEof{} -> Nothing

getText :: Token -> Text
getText tk =
  case tk of
    TkForall a b -> a <> b
    TkData a b -> a <> b
    TkCodata a b -> a <> b
    TkComma a b -> a <> b
    TkUnderscore a b -> a <> b
    TkNewline a b -> a <> b
    TkSpace a -> a
    TkBackslash a b -> a <> b
    TkVal a b -> a <> b
    TkComp a b -> a <> b
    TkFix a -> a
    TkLet a b -> a <> b
    TkWhere a b -> a <> b
    TkBind a b -> a <> b
    TkIn a b -> a <> b
    TkReturn a -> a
    TkThunk a -> a
    TkForce a -> a
    TkIdent a b -> a <> b
    TkCtor a b -> a <> b
    TkPipe a b -> a <> b
    TkDot a b -> a <> b
    TkAt a b -> a <> b
    TkLBrace a b -> a <> b
    TkRBrace a b -> a <> b
    TkLBracket a b -> a <> b
    TkRBracket a b -> a <> b
    TkLParen a b -> a <> b
    TkRParen a b -> a <> b
    TkEquals a b -> a <> b
    TkArrow a b -> a <> b
    TkCase a b -> a <> b
    TkCoCase a b -> a <> b
    TkOf a b -> a <> b
    TkSemicolon a b -> a <> b
    TkColon a b -> a <> b
    TkEof a -> a

isSpace :: Char -> Bool
isSpace = (||) <$> (== ' ') <*> (== '\t')

spaces :: Parser Text
spaces = takeWhile isSpace

reservedChar :: Char -> Bool
reservedChar '{' = True
reservedChar '}' = True
reservedChar '[' = True
reservedChar ']' = True
reservedChar '(' = True
reservedChar ')' = True
reservedChar '=' = True
reservedChar '.' = True
reservedChar ',' = True
reservedChar ' ' = True
reservedChar ':' = True
reservedChar ';' = True
reservedChar '|' = True
reservedChar _ = False

isIdentChar :: Char -> Bool
isIdentChar = (&&) <$> isAscii <*> not . reservedChar

notFollowedBy :: Show a => Parser a -> Parser ()
notFollowedBy p = optional p >>= maybe (pure ()) (fail . show)

keyword :: Text -> Parser Text
keyword w = string w <* notFollowedBy (satisfy isIdentChar)

token :: Parser Token
token =
  TkData <$> keyword "data" <*> spaces <|>
  TkCodata <$> keyword "codata" <*> spaces <|>
  TkUnderscore <$> string "_" <*> spaces <|>
  TkBackslash <$> string "\\" <*> spaces <|>
  TkForall <$> keyword "forall" <*> spaces <|>
  TkVal <$> keyword "Val" <*> spaces <|>
  TkComp <$> keyword "Comp" <*> spaces <|>
  TkNewline <$> takeWhile1 (== '\n') <*> spaces <|>
  TkSpace <$> takeWhile1 isSpace <|>
  TkFix <$> keyword "fix" <|>
  TkLet <$> keyword "let" <*> spaces <|>
  TkWhere <$> keyword "where" <*> spaces <|>
  TkBind <$> keyword "bind" <*> spaces <|>
  TkIn <$> keyword "in" <*> spaces <|>
  TkReturn <$> keyword "return" <|>
  TkForce <$> keyword "force" <|>
  TkThunk <$> keyword "thunk" <|>
  TkPipe <$> string "|" <*> spaces <|>
  TkDot <$> string "." <*> spaces <|>
  TkAt <$> string "@" <*> spaces <|>
  TkComma <$> string "," <*> spaces <|>
  TkLBrace <$> string "{" <*> spaces <|>
  TkRBrace <$> string "}" <*> spaces <|>
  TkLBracket <$> string "[" <*> spaces <|>
  (\a -> TkRBracket a "") <$> string "]" <|>
  TkLParen <$> string "(" <*> spaces <|>
  (\a -> TkRParen a "") <$> string ")" <|>
  TkSemicolon <$> string ";" <*> spaces <|>
  TkColon <$> string ":" <*> spaces <|>
  TkEquals <$> string "=" <*> spaces <|>
  TkArrow <$> string "->" <*> spaces <|>
  TkCase <$> keyword "case" <*> spaces <|>
  TkCoCase <$> keyword "cocase" <*> spaces <|>
  TkOf <$> keyword "of" <*> spaces <|>
  (\a b -> TkIdent (Text.cons a b) "") <$>
    satisfy isLower <*>
    takeWhile isIdentChar <|>
  (\a b -> TkCtor (Text.cons a b) "") <$>
    satisfy isUpper <*>
    takeWhile isIdentChar <|>
  TkEof "" <$ endOfInput

beginsTerm :: Token -> Bool
beginsTerm TkUnderscore{} = True
beginsTerm TkLParen{} = True
beginsTerm TkIdent{} = True
beginsTerm TkCtor{} = True
beginsTerm TkThunk{} = True
beginsTerm TkForce{} = True
beginsTerm TkReturn{} = True
beginsTerm TkAt{} = True
beginsTerm _ = False

tokens :: Parser [Token]
tokens = spaces *> do
  t1 <- token
  case t1 of
    TkEof{} -> pure [t1]
    _ -> do
      t2 <- token
      go t1 t2
  where
    go :: Token -> Token -> Parser [Token]
    go tt t@TkEof{} = pure [tt, t]
    go tt t@(TkSpace cs) = do
      tk <- token
      if beginsTerm tk
        then (tt :) <$> go t tk
        else
          case append tt cs of
            Nothing -> (tt :) <$> go t tk
            Just res -> fmap (res :) $ token >>= go tk
    go tt tk = fmap (tt :) $ token >>= go tk

tokenize :: Text -> Either String [Token]
tokenize = parseOnly tokens
