{-# language FlexibleContexts, GADTs #-}
module ANF where

import Prelude hiding (exp)
import Control.Monad.State (MonadState, evalState, get, put)
import Control.Monad.Writer (MonadWriter, runWriterT, tell)
import Data.Monoid (Endo(..))
import Text.PrettyPrint.ANSI.Leijen (Doc)

import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

import qualified Syntax

newtype Name = Name { unName :: String }
  deriving (Eq, Show)

data AExp
  = A_Name Name
  | A_Var !Int
  | A_Inl AExp
  | A_Inr AExp
  | A_MkProd AExp AExp
  | A_MkWith AExp AExp
  | A_MkOne
  | A_Abs Exp
  | A_Return AExp
  deriving (Eq, Show)

data CExp
  = C_Thunk AExp
  | C_Bind AExp AExp
  | C_App AExp AExp
  | C_Fst AExp
  | C_Snd AExp
  | C_SumElim AExp AExp AExp
  | C_ProdElim AExp AExp
  deriving (Eq, Show)

data Exp
  = E_Let Name CExp Exp
  | E_Force Name AExp Exp
  | E_AExp AExp
  deriving (Eq, Show)

freshName :: MonadState Int m => m Name
freshName = do
  n <- get
  Name ("name" <> show n) <$ put (n+1)

aexp :: (MonadWriter (Endo Exp) m, MonadState Int m) => Syntax.Exp a -> m AExp
aexp tm =
  case tm of
    Syntax.Var n -> pure $ A_Var n
    Syntax.Thunk a -> do
      a' <- aexp a
      n <- freshName
      tell . Endo $ E_Let n (C_Thunk a')
      pure $ A_Name n
    Syntax.Inl a _ -> A_Inl <$> aexp a
    Syntax.Inr _ a -> A_Inr <$> aexp a
    Syntax.MkProd a b -> A_MkProd <$> aexp a <*> aexp b
    Syntax.MkOne -> pure A_MkOne

    Syntax.Return a -> A_Return <$> aexp a
    Syntax.MkWith a b -> A_MkWith <$> aexp a <*> aexp b
    Syntax.Abs _ a -> A_Abs <$> exp a
    Syntax.Bind a b -> do
      a' <- aexp a
      b' <- aexp b
      n <- freshName
      tell . Endo $ E_Let n (C_Bind a' b')
      pure $ A_Name n
    Syntax.Force a -> do
      a' <- aexp a
      n <- freshName
      tell . Endo $ E_Force n a'
      pure $ A_Name n
    Syntax.SumElim a b c -> do
      a' <- aexp a
      b' <- aexp b
      c' <- aexp c
      n <- freshName
      tell . Endo $ E_Let n (C_SumElim a' b' c')
      pure $ A_Name n
    Syntax.ProdElim a b -> do
      a' <- aexp a
      b' <- aexp b
      n <- freshName
      tell . Endo $ E_Let n (C_ProdElim a' b')
      pure $ A_Name n
    Syntax.Fst a -> do
      a' <- aexp a
      n <- freshName
      tell . Endo $ E_Let n (C_Fst a')
      pure $ A_Name n
    Syntax.Snd a -> do
      a' <- aexp a
      n <- freshName
      tell . Endo $ E_Let n (C_Snd a')
      pure $ A_Name n
    Syntax.App a b -> do
      a' <- aexp a
      b' <- aexp b
      n <- freshName
      tell . Endo $ E_Let n (C_App a' b')
      pure $ A_Name n

exp :: MonadState Int m => Syntax.Exp a -> m Exp
exp e = do
  (a, Endo f) <- runWriterT $ aexp e
  pure $ f (E_AExp a)

anf :: Syntax.Exp a -> Exp
anf e = evalState (exp e) 0

prettyAExp :: AExp -> Doc
prettyAExp tm =
  case tm of
    A_Name a -> Pretty.text $ unName a
    A_Var a -> Pretty.char '#' <> Pretty.int a
    A_Inl a -> Pretty.text "inl" <> Pretty.parens (prettyAExp a)
    A_Inr a -> Pretty.text "inr" <> Pretty.parens (prettyAExp a)
    A_MkProd a b ->
      Pretty.text "prod" <>
      Pretty.parens (prettyAExp a <> Pretty.text ", " <> prettyAExp b)
    A_MkWith a b ->
      Pretty.text "with" <>
      Pretty.parens (prettyAExp a <> Pretty.text ", " <> prettyAExp b)
    A_MkOne -> Pretty.text "one"
    A_Abs a ->
      (case a of
         E_Let{} -> \x y -> x Pretty.<$> Pretty.indent 2 y
         E_Force{} -> \x y -> x Pretty.<$> Pretty.indent 2 y
         E_AExp{} -> \x y -> x <> y)
      (Pretty.text "λ. ")
      (prettyExp a)
    A_Return a -> Pretty.text "return" <> Pretty.parens (prettyAExp a)

prettyCExp :: CExp -> Doc
prettyCExp tm =
  case tm of
    C_Thunk a -> Pretty.text "thunk" <> Pretty.parens (prettyAExp a)
    C_Bind a b -> prettyAExp a <> Pretty.text "; " <> prettyAExp b
    C_App a b ->
      Pretty.text "apply" <>
      (\x y -> case a of; A_Abs{} -> x Pretty.<$> Pretty.indent 2 y; _ -> x <> y)
        (Pretty.char '(')
        (prettyAExp a <>
         (case a of; A_Abs{} -> (Pretty.<$>); _ -> (<>))
           (Pretty.text ", " )
           (prettyAExp b <> Pretty.char ')'))
    C_Fst a -> Pretty.text "fst" <> Pretty.parens (prettyAExp a)
    C_Snd a -> Pretty.text "snd" <> Pretty.parens (prettyAExp a)
    C_SumElim a b c ->
      Pretty.text "sumElim" <>
      Pretty.parens
        (prettyAExp a <>
         Pretty.text ", " <>
         prettyAExp b <>
         Pretty.text ", " <>
         prettyAExp c)
    C_ProdElim a b ->
      Pretty.text "sumElim" <>
      Pretty.parens
        (prettyAExp a <>
         Pretty.text ", " <>
         prettyAExp b)

prettyExp :: Exp -> Doc
prettyExp e =
  case e of
    E_Let a b c ->
      Pretty.hsep
      [ Pretty.text "let"
      , Pretty.text (unName a)
      , Pretty.char '='
      ] Pretty.<$>
      Pretty.indent 2 (prettyCExp b) Pretty.<$>
      Pretty.text "in" Pretty.<$>
      prettyExp c
    E_Force a b c ->
      Pretty.hsep
      [ Pretty.text "force"
      , Pretty.text (unName a)
      , Pretty.char '='
      , prettyAExp b
      , Pretty.text "in"
      ] Pretty.<$>
      prettyExp c
    E_AExp a -> prettyAExp a