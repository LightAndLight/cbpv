{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language OverloadedStrings #-}
module Lexer where

import Prelude hiding (takeWhile)

import Control.Applicative ((<|>))
import Data.Attoparsec.Text
import Data.Char (isAscii, isLower, isUpper)
import Data.Text (Text)

import qualified Data.Text as Text

data Token
  = TkForall Text Text
  | TkUnderscore Text Text
  | TkNewline Text Text
  | TkSpace Text
  | TkBackslash Text Text
  | TkValue Text Text
  | TkComputation Text Text
  | TkLet Text Text
  | TkBind Text Text
  | TkIn Text Text
  | TkReturn Text Text
  | TkThunk Text Text
  | TkForce Text Text
  | TkIdent Text Text
  | TkCtor Text Text
  | TkDot Text Text
  | TkLBrace Text Text
  | TkRBrace Text Text
  | TkLParen Text Text
  | TkRParen Text
  | TkEquals Text Text
  | TkArrow Text Text
  | TkCase Text Text
  | TkOf Text Text
  | TkSemicolon Text Text
  | TkColon Text Text
  | TkEof Text
  deriving (Eq, Ord, Show)

append :: Token -> Text -> Token
append tk txt =
  case tk of
    TkNewline a b -> TkNewline a (b <> txt)
    TkUnderscore a b -> TkUnderscore a (b <> txt)
    TkBackslash a b -> TkBackslash a (b <> txt)
    TkForall a b -> TkForall a (b <> txt)
    TkValue a b -> TkValue a (b <> txt)
    TkComputation a b -> TkComputation a (b <> txt)
    TkSpace a -> TkSpace (a <> txt)
    TkLet a b -> TkLet a (b <> txt)
    TkBind a b -> TkBind a (b <> txt)
    TkIn a b -> TkIn a (b <> txt)
    TkReturn a b -> TkReturn a (b <> txt)
    TkThunk a b -> TkThunk a (b <> txt)
    TkForce a b -> TkForce a (b <> txt)
    TkIdent a b -> TkIdent a (b <> txt)
    TkCtor a b -> TkCtor a (b <> txt)
    TkDot a b -> TkDot a (b <> txt)
    TkLBrace a b -> TkLBrace a (b <> txt)
    TkRBrace a b -> TkRBrace a (b <> txt)
    TkLParen a b -> TkLParen a (b <> txt)
    TkRParen a -> TkRParen (a <> txt)
    TkEquals a b -> TkEquals a (b <> txt)
    TkArrow a b -> TkArrow a (b <> txt)
    TkCase a b -> TkCase a (b <> txt)
    TkOf a b -> TkOf a (b <> txt)
    TkSemicolon a b -> TkSemicolon a (b <> txt)
    TkColon a b -> TkColon a (b <> txt)
    TkEof a -> TkEof (a <> txt)

isSpace :: Char -> Bool
isSpace = (||) <$> (== ' ') <*> (== '\t')

spaces :: Parser Text
spaces = takeWhile isSpace

reservedChar :: Char -> Bool
reservedChar '{' = True
reservedChar '}' = True
reservedChar '(' = True
reservedChar ')' = True
reservedChar '=' = True
reservedChar '.' = True
reservedChar ' ' = True
reservedChar _ = False

token :: Parser Token
token =
  TkUnderscore <$> string "_" <*> spaces <|>
  TkBackslash <$> string "\\" <*> spaces <|>
  TkForall <$> string "forall" <*> spaces <|>
  TkValue <$> string "Value" <*> spaces <|>
  TkComputation <$> string "Computation" <*> spaces <|>
  TkNewline <$> takeWhile1 (== '\n') <*> spaces <|>
  TkSpace <$> takeWhile1 isSpace <|>
  TkLet <$> string "let" <*> spaces <|>
  TkBind <$> string "bind" <*> spaces <|>
  TkIn <$> string "in" <*> spaces <|>
  TkReturn <$> string "return" <*> spaces <|>
  TkThunk <$> string "thunk" <*> spaces <|>
  TkForce <$> string "force" <*> spaces <|>
  TkDot <$> string "." <*> spaces <|>
  TkLBrace <$> string "{" <*> spaces <|>
  TkRBrace <$> string "}" <*> spaces <|>
  TkLParen <$> string "(" <*> spaces <|>
  TkRParen <$> string ")" {- spaces deliberately omitted -} <|>
  TkSemicolon <$> string ";" <*> spaces <|>
  TkColon <$> string ":" <*> spaces <|>
  TkEquals <$> string "=" <*> spaces <|>
  TkArrow <$> string "->" <*> spaces <|>
  TkCase <$> string "case" <*> spaces <|>
  TkOf <$> string "of" <*> spaces <|>
  (\a b -> TkIdent (Text.cons a b) "") <$>
    satisfy isLower <*>
    takeWhile ((&&) <$> isAscii <*> not . reservedChar) <|>
  (\a b -> TkCtor (Text.cons a b) "") <$>
    satisfy isUpper <*>
    takeWhile ((&&) <$> isAscii <*> not . reservedChar) <|>
  TkEof "" <$ endOfInput

beginsTerm :: Token -> Bool
beginsTerm TkUnderscore{} = True
beginsTerm TkLParen{} = True
beginsTerm TkIdent{} = True
beginsTerm _ = False

tokens :: Parser [Token]
tokens = spaces *> do
  t1 <- token
  t2 <- token
  go t1 t2
  where
    go :: Token -> Token -> Parser [Token]
    go tt t@TkEof{} = pure [tt, t]
    go tt t@(TkSpace cs) = do
      tk <- token
      if beginsTerm tk
        then (tt :) <$> go t tk
        else fmap (append tt cs :) $ token >>= go tk
    go tt tk = fmap (tt :) $ token >>= go tk

tokenize :: Text -> Either String [Token]
tokenize = parseOnly tokens
