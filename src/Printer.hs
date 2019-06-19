{-# language GADTs #-}
module Printer where

import Text.PrettyPrint.ANSI.Leijen (Doc)
import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Text as Text

import Syntax

prettyPat :: Pattern -> Doc
prettyPat PWild = Pretty.char '_'
prettyPat PVar = Pretty.text "v0"
prettyPat (PCtor n arity) =
  Pretty.text (Text.unpack n) <>
  Pretty.space <>
  Pretty.hsep vs
  where
    vs = take arity $ Pretty.text . ('v' :) . show <$> [0::Int ..]

prettyExp :: Exp a -> Doc
prettyExp tm =
  case tm of
    Ann a b ->
      (case a of
         Abs{} -> Pretty.parens
         _ -> id)
      (prettyExp a) <>
      Pretty.text " : " <>
      prettyTy b
    Var a -> Pretty.char '#' <> Pretty.int a
    Thunk a ->
      Pretty.text "thunk " <>
      (case a of
         App{} -> Pretty.parens
         Abs{} -> Pretty.parens
         Return{} -> Pretty.parens
         Fst{} -> Pretty.parens
         Snd{} -> Pretty.parens
         Force{} -> Pretty.parens
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         Case{} -> Pretty.parens
         _ -> id)
      (prettyExp a)
    Ctor a [] -> Pretty.text (Text.unpack a)
    Ctor a bs ->
      foldl
        (\rest x ->
           rest <>
           (case x of
              Thunk{} -> Pretty.parens
              Ctor _ (_:_) -> Pretty.parens
              _ -> id)
           (prettyExp x))
        (Pretty.text $ Text.unpack a)
        bs
    Return a ->
      Pretty.text "return " <>
      (case a of
         Thunk{} -> Pretty.parens
         Ctor _ (_:_) -> Pretty.parens
         _ -> id)
      (prettyExp a)
    MkWith a b ->
      Pretty.text "with " <>
      (case a of
         App{} -> Pretty.parens
         Abs{} -> Pretty.parens
         Return{} -> Pretty.parens
         Fst{} -> Pretty.parens
         Snd{} -> Pretty.parens
         Force{} -> Pretty.parens
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         Case{} -> Pretty.parens
         _ -> id)
      (prettyExp a) <>
      Pretty.space <>
      (case b of
         App{} -> Pretty.parens
         Abs{} -> Pretty.parens
         Return{} -> Pretty.parens
         Fst{} -> Pretty.parens
         Snd{} -> Pretty.parens
         Force{} -> Pretty.parens
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         Case{} -> Pretty.parens
         _ -> id)
      (prettyExp b)
    Abs a b ->
      Pretty.text "\\( :" <> prettyTy a <> Pretty.text ") -> " <>
      prettyExp b
    Bind a b ->
      Pretty.text "bind= " <>
      (case a of
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         _ -> id)
      (prettyExp a) <>
      Pretty.text " in" Pretty.<$>
      prettyExp b
    Let a b ->
      Pretty.text "let= " <>
      prettyExp a <>
      Pretty.text " in" Pretty.<$>
      prettyExp b
    Force a ->
      Pretty.text "force " <>
      (case a of
         Thunk{} -> Pretty.parens
         Ctor _ (_:_) -> Pretty.parens
         _ -> id)
      (prettyExp a)
    Case a bs ->
      Pretty.text "case " <>
      prettyExp a <>
      Pretty.text "of" Pretty.<$>
      Pretty.indent 2
        (Pretty.vsep . NonEmpty.toList $
         (\(Branch p e) ->
            prettyPat p <> Pretty.text " -> " <> prettyExp e) <$> bs)
    Fst a ->
      Pretty.text "fst " <>
      (case a of
         App{} -> Pretty.parens
         Abs{} -> Pretty.parens
         Return{} -> Pretty.parens
         Fst{} -> Pretty.parens
         Snd{} -> Pretty.parens
         Force{} -> Pretty.parens
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         Case{} -> Pretty.parens
         _ -> id)
      (prettyExp a)
    Snd a ->
      Pretty.text "snd " <>
      (case a of
         App{} -> Pretty.parens
         Abs{} -> Pretty.parens
         Return{} -> Pretty.parens
         Fst{} -> Pretty.parens
         Snd{} -> Pretty.parens
         Force{} -> Pretty.parens
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         Case{} -> Pretty.parens
         _ -> id)
      (prettyExp a)
    App a b ->
      Pretty.space <>
      (case a of
         Abs{} -> Pretty.parens
         Return{} -> Pretty.parens
         Fst{} -> Pretty.parens
         Snd{} -> Pretty.parens
         Force{} -> Pretty.parens
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         Case{} -> Pretty.parens
         _ -> id)
      (prettyExp a) <>
      Pretty.space <>
      (case b of
         Thunk{} -> Pretty.parens
         Ctor _ (_:_) -> Pretty.parens
         _ -> id)
      (prettyExp b)

prettyTy :: Ty -> Doc
prettyTy ty =
  case ty of
    TApp (TApp With a) b ->
      (case a of
         TApp (TApp Arrow _) _ -> Pretty.parens
         _ -> id)
      (prettyTy a) <>
      Pretty.text " & " <>
      (case b of
         TApp (TApp Arrow _) _ -> Pretty.parens
         _ -> id)
      (prettyTy b)
    TApp (TApp Arrow a) b ->
      (case a of
         TApp (TApp Arrow _) _ -> Pretty.parens
         _ -> id)
      (prettyTy a) <>
      Pretty.text " -> " <>
      prettyTy b
    TApp a b ->
      (case a of
         TApp (TApp Arrow _) _ -> Pretty.parens
         _ -> id)
      (prettyTy a) <>
      Pretty.space <>
      (case b of
         TApp{} -> Pretty.parens
         _ -> id)
      (prettyTy b)
    U -> Pretty.char 'U'
    TInd a -> Pretty.text $ Text.unpack a
    F -> Pretty.char 'F'
    With -> Pretty.text "(&)"
    Arrow -> Pretty.text "(->)"
    TVar a -> Pretty.char '#' <> Pretty.int a