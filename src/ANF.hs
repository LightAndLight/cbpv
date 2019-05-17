module ANF where

import Prelude hiding (exp)

import qualified Syntax

data AExp
  = A_Ix !Int
  | A_Inl AExp
  | A_Inr AExp
  | A_MkProd AExp AExp
  | A_MkOne
  | A_Lam Exp
  deriving (Eq, Show)

data CExp
  = C_Thunk AExp
  | C_Force AExp
  | C_Return AExp
  | C_Bind AExp AExp
  | C_App AExp AExp
  | C_Fst AExp
  | C_Snd AExp
  | C_SumElim AExp AExp AExp
  | C_ProdElim AExp AExp
  deriving (Eq, Show)

data Exp
  = E_Let CExp Exp
  | E_AExp AExp
  deriving (Eq, Show)

aexp :: Syntax.Exp a -> AExp
aexp = _

exp :: Syntax.Exp a -> CExp
exp = _

anf :: Syntax.Exp a -> Exp
anf e = _
