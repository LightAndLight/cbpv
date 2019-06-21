module Compile where

{-

Val *is*    -  data
Comp *does* -  code

x : T (Ann)            - erased
x (Var)                - offset into stack
thunk[c] (Thunk)       - address of code(c)
Ctor[...] (Ctor)       - struct
return[x] (Return)     - produce x as a result
\(x : T) -> e (Abs)    - code(e), expecting a T on top of the stack
bind x = a in b (Bind) - run code(a), push its result, run code(b)
let x = a in b (Let)   - push a, run code(b)
fix f : T in e (Fix)   - push the start address of code(e), run code(e)
Case - 

-}