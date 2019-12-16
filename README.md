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

* Syntax
  * `#` (thunk) takes a `a : Comp` and produces a `U a : Val`
  * `^` (force) takes a `U a : Val` and produces a `a : Comp`

## Examples

(actual syntax) (braces are how I ignore layout rules)

```
data Sum (a : Val) (b : Val) = Left[a] | Right[b]

sumElim = {
  #
    \@(a : Val) ->
    \@(b : Val) ->
    \@(r : Comp) ->
    \(f : U (a -> r)) ->
    \(g : U (b -> r)) ->
    \(x : Sum a b) ->
    case x of { 
      Left[a] -> ^f a; 
      Right[a] -> ^g a 
    } 
}

data Tensor (a : Val) (b : Val) = Tensor[a, b]

tensorElim = {
  #
    \@(a : Val) ->
    \@(b : Val) ->
    \@(r : Comp) ->
    \(f : U (a -> b -> r)) ->
    \(x : Tensor a b) -> 
    case x of { Tensor[a, b] -> ^f a b } 
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

takeS = {
  #
    \@(a : Comp) ->
    fix self : U (forall (a : Comp). Nat -> U (Stream a) -> F (List (U a))) in
    \(n : Nat) ->
    \(s : U (Stream a)) -> 
    case n of { 
      Z -> return[Nil[]]; 
      S[k] -> 
        bind 
          rest = self k (# ^s.tail)
        in 
          return[ Cons[ # ^s.head ], rest ] ]
    }
}

codata Infinity where { next : Infinity }
  
infinity = # fix self : U Infinity in cocase Infinity of { next -> ^self }

countFrom = {
  #
    fix self : U (Nat -> Stream (F Nat))) in
    \(n : Nat) -> 
    cocase Stream (F Nat) of { 
      head -> return[n]; 
      tail -> ^self S[n]
    }
}
```
