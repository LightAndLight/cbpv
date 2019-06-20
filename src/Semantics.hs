{-# language DataKinds, GADTs #-}
module Semantics where

import Data.List.NonEmpty (NonEmpty(..))
import Data.Text (Text)

import Syntax

data Terminal
  = TReturn (Exp 'V)
  | TAbs (Exp 'C)
  | TCoCase (NonEmpty CoBranch)
  deriving Show

findBranch :: Text -> [Exp 'V] -> NonEmpty (Branch a) -> Exp a
findBranch n args (b :| bs) = go (b : bs)
  where
    go [] = error "stuck: incomplete pattern match"
    go (Branch p e : xs) =
      case p of
        PWild -> e
        PVar _ -> inst e (Ctor n args)
        PCtor n' arity _ ->
          if n == n'
          then
            if arity == length args
            then subst (args !!) e
            else error "stuck: findBranch"
          else go xs

findCoBranch :: Text -> NonEmpty CoBranch -> Exp 'C
findCoBranch n (b :| bs) = go (b:bs)
  where
    go [] = error "stuck: incomplete copattern match"
    go (CoBranch n' e : cs) =
      if n == n'
      then e
      else go cs

eval :: Exp 'C -> Terminal
eval c =
  case c of
    Ann a _ -> eval a
    Return a -> TReturn a
    Abs _ _ a -> TAbs a
    Bind _ a b ->
      case eval a of
        TReturn x -> eval $ inst b x
        _ -> error "stuck: bind"
    Let _ a b -> eval $ inst b a
    Fix a -> eval $ App a (Thunk $ Fix a)
    Force (Thunk x) -> eval x
    Force{} -> error "stuck: force"
    Case (Ctor n as) bs -> eval $ findBranch n as bs
    Case{} -> error "stuck: case"
    CoCase _ bs -> TCoCase bs
    Dtor n a ->
      case eval a of
        TCoCase bs -> eval $ findCoBranch n bs
        _ -> error "stuck: dtor"
    App a b ->
      case eval a of
        TAbs x -> eval $ inst x b
        _ -> error "stuck: app"