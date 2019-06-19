{-# language DataKinds, GADTs #-}
module Semantics where

import Data.List.NonEmpty (NonEmpty(..))
import Data.Text (Text)

import Syntax

data Terminal
  = TReturn (Exp 'V)
  | TAbs (Exp 'C)
  | TMkWith (Exp 'C) (Exp 'C)
  deriving Show

findBranch :: Text -> [Exp 'V] -> NonEmpty Branch -> Exp 'C
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

eval :: Exp 'C -> Terminal
eval c =
  case c of
    Ann a _ -> eval a
    Return a -> TReturn a
    MkWith a b -> TMkWith a b
    Abs _ _ a -> TAbs a
    Bind _ a b ->
      case eval a of
        TReturn x -> eval $ inst b x
        _ -> error "stuck: bind"
    Let _ a b -> eval $ inst b a
    Force (Thunk x) -> eval x
    Force{} -> error "stuck: force"
    Case (Ctor n as) bs -> eval $ findBranch n as bs
    Case{} -> error "stuck: case"
    Fst a ->
      case eval a of
        TMkWith x _ -> eval x
        _ -> error "stuck: fst"
    Snd a ->
      case eval a of
        TMkWith _ x -> eval x
        _ -> error "stuck: snd"
    App a b ->
      case eval a of
        TAbs x -> eval $ inst x b
        _ -> error "stuck: app"