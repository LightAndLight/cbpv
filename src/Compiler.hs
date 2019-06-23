module Compiler where

import Data.Void (Void)
import System.Exit (exitFailure)
import System.Environment (getArgs)
import Text.Megaparsec (ParseErrorBundle, errorBundlePretty)

import qualified Data.Text.IO as Text

import Lexer
import Parser
import Typecheck

run :: IO ()
run = do
  file:_ <- getArgs
  src <- Text.readFile file
  lexRes <- handleLexError $ tokenize src
  parseRes <- handleParseError $ parse file module_ (Tokens lexRes)
  _ <- handleTypecheckError $ tc (checkModule parseRes) emptyTCEnv
  putStrLn "Success"
  where
    handleLexError :: Either String a -> IO a
    handleLexError (Left e) = do
      putStrLn $ "Lexical error: " <> e
      exitFailure
    handleLexError (Right a) = pure a

    handleParseError :: Either (ParseErrorBundle Tokens Void) a -> IO a
    handleParseError (Left e) = do
      putStrLn $ "Parse error: " <> errorBundlePretty e
      exitFailure
    handleParseError (Right a) = pure a

    handleTypecheckError :: Either TCError a -> IO a
    handleTypecheckError (Left e) = do
      putStrLn $ "Typecheck error: " <> show e
      exitFailure
    handleTypecheckError (Right a) = pure a