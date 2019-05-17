{-# language DataKinds, GADTs #-}
module Semantics where

import Syntax

data Terminal
  = TReturn (Exp 'V)
  | TAbs (Exp 'C)
  | TMkWith (Exp 'C) (Exp 'C)
  deriving (Eq, Show)

eval :: Exp 'C -> Terminal
eval c =
  case c of
    Return a -> TReturn a
    MkWith a b -> TMkWith a b
    Abs _ a -> TAbs a
    Bind a b -> do
      case eval a of
        TReturn x -> eval $ inst b x
        _ -> error "stuck: bind"
    Force (Thunk x) -> eval x
    Force{} -> error "stuck: force"
    SumElim g _ (Inl a _) -> eval $ inst g a
    SumElim _ h (Inr _ a) -> eval $ inst h a
    SumElim{} -> error "stuck: sumElim"
    ProdElim g (MkProd a b) -> eval $ inst (inst g a) b
    ProdElim{} -> error "stuck: prodElim"
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