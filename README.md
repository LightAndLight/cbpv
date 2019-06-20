# cbpv

A usable type system for call by push-value:

* Kinds
  * The `*` kind is split in two: `Val` (values) and `Comp` (computations)
  * `U : Comp -> Val`
  * `F : Val -> Comp`
  * `(->) : Val -> Comp -> Comp`
  * etc.
  * Top-level definitions must be `Val`s
* User-definable datatypes
  * Currently require kind annotations (but this is simple to remove)
  * Inductive datatypes inhabit the `Val` kind
    * Only carries around other values
    * Constructors are not functions (functions only return computations),
      so constructors must be fully applied
    * Generalised elimination using `case ... of`
  * Coinductive datatypes inhabit the `Comp` kind
    * Can only produce computations (unsure)
    * Destructors are not functions
    * Generalised introduction using `cocase ... of`

## Examples

(Doesn't parse, yet) (braces are how I ignore layout rules)

```
data Sum (a : Val) (b : Val) = Left[a] | Right[b]

sumElim = {
  thunk[ 
    \@(a : Val) ->
    \@(b : Val) ->
    \@(r : Comp) ->
    \(f : U (a -> r)) ->
    \(g : U (b -> r)) ->
    \(x : Sum a b) ->
    case x of { 
      Left[a] -> force[f] a; 
      Right[a] -> force[g] a 
    } 
  ]
}

data Tensor (a : Val) (b : Val) = Tensor[a, b]

tensorElim = {
  thunk[ 
    \@(a : Val) ->
    \@(b : Val) ->
    \@(r : Comp) ->
    \(f : U (a -> b -> r)) ->
    \(x : Tensor a b) -> 
    case x of { Tensor[a, b] -> force[f] a b } 
  ]
}

data Nat = Z[] | S[Nat]

data List (a : Val) = Nil[] | Cons[a, List a]

codata Pair (a : Comp) (b : Comp) where {
  fst : a;
  snd : b
}

codata Stream (a : Comp) where {
  head : a;
  tail : Stream a
}

takeS : U (forall (a : Comp). Nat -> U (Stream a) -> F (List (U a)))
takeS = {
  thunk[
  \@(a : Comp) ->
  fix[
    \(rec : U (forall (a : Comp). Nat -> U (Stream a) -> F (List (U a)))) ->
    \(n : Nat) ->
    \(s : U (Stream a) n -> 
    case n of { 
      Z -> return[Nil[]]; 
      S[k] -> 
        bind 
          rest = rec k thunk[ force[s].tail ]
        in 
          return[ Cons[ thunk[ force[s].head ], rest ] ]
    }
  ]
  ]
}

codata AlephNull where { next : AlephNull }
  
infinity : U AlephNull
infinity = thunk[ cocase AlephNull of { next -> force[infinity] } ]

countFrom : U (Nat -> Stream (F Nat))
countFrom = {
  thunk[
  fix[
    \(rec : U (Nat -> Stream (F Nat))) ->
    \(n : Nat) -> 
    cocase Stream (F Nat) of { 
      head -> return[n]; 
      tail -> force[rec] S[n]
    }
  ]
  ]
}
```
