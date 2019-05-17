module Semantics where

import Syntax

data Terminal
  = TReturn V
  | TAbs C
  | TMkWith C C
  deriving (Eq, Show)

eval :: C -> Terminal
eval c =
  case c of
    Return a -> TReturn a
    MkWith a b -> TMkWith a b
    Abs _ a -> TAbs a
    Bind a b -> do
      case eval a of
        TReturn x -> eval $ instC b x
        _ -> error "stuck: bind"
    Force (Thunk x) -> eval x
    Force{} -> error "stuck: force"
    SumElim g _ (Inl a _) -> eval $ instC g a
    SumElim _ h (Inr _ a) -> eval $ instC h a
    SumElim{} -> error "stuck: sumElim"
    ProdElim g (MkProd a b) -> eval $ instC (instC g a) b
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
        TAbs x -> eval $ instC x b
        _ -> error "stuck: app"