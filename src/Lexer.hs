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
  | TkComma Text Text
  | TkUnderscore Text Text
  | TkNewline Text Text
  | TkSpace Text
  | TkBackslash Text Text
  | TkVal Text Text
  | TkComp Text Text
  | TkFix Text
  | TkLet Text Text
  | TkBind Text Text
  | TkIn Text Text
  | TkReturn Text
  | TkThunk Text
  | TkForce Text
  | TkIdent Text Text
  | TkCtor Text Text
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
    TkBind a b -> Just $ TkBind a (b <> txt)
    TkIn a b -> Just $ TkIn a (b <> txt)
    TkReturn{} -> Nothing
    TkThunk{} -> Nothing
    TkForce{} -> Nothing
    TkIdent a b -> Just $ TkIdent a (b <> txt)
    TkCtor a b -> Just $ TkCtor a (b <> txt)
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
reservedChar _ = False

token :: Parser Token
token =
  TkUnderscore <$> string "_" <*> spaces <|>
  TkBackslash <$> string "\\" <*> spaces <|>
  TkForall <$> string "forall" <*> spaces <|>
  TkVal <$> string "Val" <*> spaces <|>
  TkComp <$> string "Comp" <*> spaces <|>
  TkNewline <$> takeWhile1 (== '\n') <*> spaces <|>
  TkSpace <$> takeWhile1 isSpace <|>
  TkFix <$> string "fix" <|>
  TkLet <$> string "let" <*> spaces <|>
  TkBind <$> string "bind" <*> spaces <|>
  TkIn <$> string "in" <*> spaces <|>
  TkReturn <$> string "return" <|>
  TkForce <$> string "force" <|>
  TkThunk <$> string "thunk" <|>
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
  TkCase <$> string "case" <*> spaces <|>
  TkCoCase <$> string "cocase" <*> spaces <|>
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
