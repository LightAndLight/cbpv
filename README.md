# cbpv

A usable type system for call by push-value:

* Kinds
  * The `*` kind is split in two: `Value` and `Computation`
  * `U : Computation -> Value`
  * `F : Value -> Computation`
  * `(->) : Value -> Computation -> Computation`
  * etc.
  * Top-level definitions must be `Value`s
* User-definable datatypes
  * Currently require kind annotations (but this is simple to remove)
  * Inductive datatypes inhabit the `Value` kind
    * Only carries around other values
    * Constructors are not functions (functions only return computations),
      so constructors must be fully applied
    * Generalised elimination using `case ... of`
  * Coinductive datatypes inhabit the `Computation` kind
    * Can only produce computations (unsure)
    * Destructors are not functions (unsure) (functions only take values as arguments)
    * Generalised introduction using `TBA`

## Examples

(Doesn't parse, yet) (braces are how I ignore layout rules)

```
data Sum (a : Value) (b : Value) = Left a | Right b

sumElim : {
  U (
    forall (a : Value) (b : Value) (r : Computation).
    U (a -> r) ->
    U (b -> r) ->
    Sum a b -> r
  )
}
sumElim f g x = {
  thunk (case x of { Left a -> force f a; Right a -> force g a })
}

data Tensor (a : Value) (b : Value) = Tensor a b

tensorElim : {
  U (
    forall (a : Value) (b : Value) (r : Computation).
    U (a -> b -> r) ->
    Tensor a b -> r
  )
}
tensorElim f x = thunk (case x of { Tensor a b -> force f a b })

data Nat = Z | S Nat

data List (a : Value) = Nil | Cons a (List a)

codata Pair (a : Computation) (b : Computation) where {
  fst : a;
  snd : b
}

codata Stream (a : Computation) where {
  head : a;
  tail : Stream a
}

takeS : {
  U (
    forall (a : Computation). 
    Nat -> 
    U (Stream a) -> 
    F (List (U a))
  )
}
takeS n s = {
  case n of { 
    Z -> return Nil; 
    S k -> 
      bind 
        rest = takeS k (thunk (tail (force s))) 
      in 
        return (Cons (thunk (head (force s))) rest)
  }
}

codata AlephNull where { next : AlephNull }
  
infinity : U AlephNull
infinity = thunk (cocase AlephNull of { next -> infinity })

countFrom : U (Nat -> Stream (F Nat))
countFrom n = {
  thunk (
    cocase Stream (F Nat) of { 
      head -> return n; 
      tail -> force countFrom (S n) 
    }
  )
}
```
