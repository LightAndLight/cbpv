{-# language DataKinds, GADTs #-}
{-# language RecursiveDo #-}
module Semantics.CBNeed where

import Control.Monad.State (State, get, put)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import Data.Text (Text)

import qualified Data.Map as Map

import Syntax

data Terminal
  = TReturn (Exp 'V)
  | TAbs (Exp 'C)
  | TAbsTy (Exp 'C)
  | TCoCase (NonEmpty CoBranch)
  deriving Show

data Cell = Hole | Suspend (Exp 'C) | Value Terminal
  deriving Show

newtype Heap = Heap (Map Int Cell)
  deriving Show

newHeap :: Heap
newHeap = Heap mempty

alloc :: Exp 'C -> State Heap Int
alloc e = do
  Heap h <- get
  let n = Map.size h
  put . Heap $ Map.insert n (Suspend e) h
  pure n

maybeAlloc :: Exp 'V -> State Heap (Exp 'V)
maybeAlloc (Thunk a) = Addr <$> alloc a
maybeAlloc a = pure a

findBranch :: Text -> [Exp 'V] -> NonEmpty (Branch a) -> State Heap (Exp a)
findBranch n args (b :| bs) = go (b : bs)
  where
    go [] = error "stuck: incomplete pattern match"
    go (Branch p e : xs) =
      case p of
        PWild -> pure e
        PVar _ -> pure $ inst e (Ctor n args)
        PCtor n' arity _ ->
          if n == n'
          then
            if arity == length args
            then do
              args' <- traverse maybeAlloc args
              pure $ subst (args' !!) e
            else error "stuck: findBranch"
          else go xs

findCoBranch :: Text -> [Exp 'V] -> NonEmpty CoBranch -> State Heap (Exp 'C)
findCoBranch n args (b :| bs) = go (b:bs)
  where
    go [] = error "stuck: incomplete copattern match"
    go (CoBranch n' arity _ _ e : cs) =
      if n == n'
      then
        if arity == length args
        then do
          args' <- traverse maybeAlloc args
          pure $ subst (args' !!) e
        else error "stuck: findCoBranch"
      else go cs

eval :: Exp 'C -> State Heap Terminal
eval tm =
  case tm of
    Ann a _ -> eval a
    Return a -> pure $ TReturn a
    Abs _ _ a -> pure $ TAbs a
    Bind _ a b -> do
      a' <- eval a
      case a' of
        TReturn x -> do
          x' <- maybeAlloc x
          eval $ inst b x'
        _ -> error "stuck: bind"
    AbsTy _ _ a -> pure $ TAbsTy a
    AppTy a ty -> do
      a' <- eval a
      case a' of
        TAbsTy b -> eval $ instTyExp b ty
        _ -> error "stuck: appTy"
    Let _ a b -> do
      a' <- maybeAlloc a
      eval $ inst b a'
    Fix _ _ a -> do
      rec
        let a' = inst a (Addr n)
        n <- alloc a'
      eval a'
    Force (Thunk x) -> eval x
    Force (Addr x) -> do
      Heap h <- get
      case Map.lookup x h of
        Nothing -> error "stuck: force addr"
        Just c ->
          case c of
            Hole -> error "infinite loop"
            Value a -> pure a
            Suspend a -> do
              put . Heap $ Map.insert x Hole h
              res <- eval a
              put . Heap $ Map.insert x (Value res) h
              pure res
    Force{} -> error "stuck: force"
    Case (Ctor n as) bs -> eval =<< findBranch n as bs
    Case{} -> error "stuck: case"
    CoCase _ bs -> pure $ TCoCase bs
    Dtor n as b -> do
      b' <- eval b
      case b' of
        TCoCase bs -> eval =<< findCoBranch n as bs
        _ -> error "stuck: dtor"
    App a b -> do
      a' <- eval a
      case a' of
        TAbs x -> do
          b' <- maybeAlloc b
          eval $ inst x b'
        _ -> error "stuck: app"
