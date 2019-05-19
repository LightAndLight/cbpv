{-# language FlexibleContexts #-}
module Lifted where

import Control.Monad.State (MonadState, get, gets, put, modify)
import Control.Monad.Writer (MonadWriter, runWriter, runWriterT, tell)
import Data.Map (Map)
import Data.Set (Set)

import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified ANF

newtype Fun = Fun { unFun :: String }
  deriving (Eq, Show)

data Decl
  = DeclFun Fun [Decl] Exp
  deriving (Eq, Show)

data Exp
  = L_Name ANF.Name
  | L_Arg
  | L_Lookup !Int
  | L_Inl Exp
  | L_Inr Exp
  | L_MkProd Exp Exp
  | L_MkWith Exp Exp
  | L_MkOne
  | L_Closure Fun [Exp]
  | L_Return Exp
  deriving (Eq, Show)

data Program = Program [Decl] Exp
  deriving (Eq, Show)

type Ctx = (Int, Map Int Int)

freshFun :: MonadState Ctx m => m Fun
freshFun = do
  (n, xx) <- get
  Fun ("fun" <> show n) <$ put (n+1, xx)

type Env = ([Decl], Set Int)

liftAExp :: (MonadState Ctx m, MonadWriter Env m) => ANF.AExp -> m Exp
liftAExp tm =
  case tm of
    ANF.A_Name a -> pure $ L_Name a
    ANF.A_Var 0 -> pure L_Arg
    ANF.A_Var n -> do
      (xx, m) <- get
      v <-
        case Map.lookup n m of
          Nothing -> do
            let v = Map.size m
            v <$ put (xx, Map.insert n (Map.size m) m)
          Just v -> pure v
      tell (mempty, _)
      pure $ L_Lookup v
    ANF.A_Inl a -> L_Inl <$> liftAExp a
    ANF.A_Inr a -> L_Inr <$> liftAExp a
    ANF.A_MkProd a b -> L_MkProd <$> liftAExp a <*> liftAExp b
    ANF.A_MkWith a b -> L_MkWith <$> liftAExp a <*> liftAExp b
    ANF.A_MkOne -> pure L_MkOne
    ANF.A_Abs a -> do
      name <- freshFun
      (a', (decls, frees)) <- runWriterT (liftExp a)
      tell ([DeclFun name decls a'], mempty)
      let closure = Set.foldr (\a b -> if a == 0 then b else L_Var (a-1) : b) [] frees
      pure $ L_Closure name closure
    ANF.A_Return a -> L_Return <$> liftAExp a

liftCExp :: MonadWriter Env m => ANF.CExp -> m Exp
liftCExp = _

liftExp :: MonadWriter Env m => ANF.Exp -> m Exp
liftExp = _

lambdaLift :: ANF.Exp -> Program
lambdaLift e = Program decls a
  where
    (a, (decls, frees)) = runWriter (liftExp e)