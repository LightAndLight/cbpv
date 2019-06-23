module Compiler where

import System.Exit (exitFailure)
import System.Environment (getArgs)
import Text.Trifecta.Result (Result(..), _errDoc)

import qualified Data.ByteString as ByteString

import Parser
import Typecheck

run :: IO ()
run = do
  file:_ <- getArgs
  src <- ByteString.readFile file
  parseRes <- handleParseError $ parse file module_ src
  _ <- handleTypecheckError $ tc (checkModule parseRes) emptyTCEnv
  print parseRes
  where
    handleParseError :: Result a -> IO a
    handleParseError (Failure e) = do
      putStrLn $ "Parse error: \n" <> show (_errDoc e)
      exitFailure
    handleParseError (Success a) = pure a

    handleTypecheckError :: Either TCError a -> IO a
    handleTypecheckError (Left e) = do
      putStrLn $ "Typecheck error: " <> show e
      exitFailure
    handleTypecheckError (Right a) = pure a
