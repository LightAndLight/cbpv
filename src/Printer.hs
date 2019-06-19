{-# language GADTs #-}
{-# language LambdaCase #-}
module Printer where

import Data.Maybe (fromMaybe)
import Text.PrettyPrint.ANSI.Leijen (Doc)
import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Text as Text

import Syntax

prettyPat :: Pattern -> Doc
prettyPat PWild = Pretty.char '_'
prettyPat (PVar n) =
  Pretty.text $ maybe "<unnamed>" Text.unpack n
prettyPat p@(PCtor n _ _) =
  Pretty.text (Text.unpack n) <>
  Pretty.space <>
  Pretty.hsep vs
  where
    vs = Pretty.text . Text.unpack <$> patNames p

prettyExp :: (Int -> Maybe Doc) -> Exp a -> Doc
prettyExp names tm =
  case tm of
    Name a -> Pretty.text $ Text.unpack a
    Ann a b ->
      (case a of
         Abs{} -> Pretty.parens
         Case{} -> Pretty.parens
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         _ -> id)
      (prettyExp names a) <>
      Pretty.text " : " <>
      prettyTy (const Nothing) b
    Var a ->
      fromMaybe (Pretty.char '#' <> Pretty.int a) $ names a
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
      (prettyExp names a)
    Ctor a [] -> Pretty.text (Text.unpack a)
    Ctor a bs ->
      foldl
        (\rest x ->
           rest <>
           (case x of
              Thunk{} -> Pretty.parens
              Ctor _ (_:_) -> Pretty.parens
              _ -> id)
           (prettyExp names x))
        (Pretty.text $ Text.unpack a)
        bs
    Return a ->
      Pretty.text "return " <>
      (case a of
         Thunk{} -> Pretty.parens
         Ctor _ (_:_) -> Pretty.parens
         _ -> id)
      (prettyExp names a)
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
      (prettyExp names a) <>
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
      (prettyExp names b)
    Abs name a b ->
      let m_ndoc = Pretty.text . Text.unpack <$> name in
      Pretty.text "\\(" <>
      foldMap (<> Pretty.space) m_ndoc <>
      Pretty.text ": " <>
      prettyTy (const Nothing) a <>
      Pretty.text ") -> " <>
      prettyExp (\case; 0 -> m_ndoc; n -> names (n-1)) b
    Bind name a b ->
      let m_ndoc = Pretty.text . Text.unpack <$> name in
      Pretty.text "bind" <>
      foldMap (\x -> Pretty.space <> x <> Pretty.space) m_ndoc <>
      Pretty.text "= " <>
      (case a of
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         _ -> id)
      (prettyExp names a) <>
      Pretty.text " in" Pretty.<$>
      prettyExp (\case; 0 -> m_ndoc; n -> names (n-1)) b
    Let name a b ->
      let m_ndoc = Pretty.text . Text.unpack <$> name in
      Pretty.text "let" <>
      foldMap (\x -> Pretty.space <> x <> Pretty.space) m_ndoc <>
      Pretty.text "= " <>
      prettyExp names a <>
      Pretty.text " in" Pretty.<$>
      prettyExp (\case; 0 -> m_ndoc; n -> names (n-1)) b
    Force a ->
      Pretty.text "force " <>
      (case a of
         Thunk{} -> Pretty.parens
         Ctor _ (_:_) -> Pretty.parens
         _ -> id)
      (prettyExp names a)
    Case a bs ->
      Pretty.text "case " <>
      prettyExp names a <>
      Pretty.text " of {" Pretty.<$>
      Pretty.indent 2
        (Pretty.vsep . NonEmpty.toList $
         (\(Branch p e) ->
            let arity = patArity p in
            prettyPat p <>
            Pretty.text " -> " <>
            prettyExp
              (\n ->
                 if n < arity
                 then Just $ fmap (Pretty.text . Text.unpack) (patNames p) !! n
                 else names (n-arity))
              e) <$> bs) Pretty.<$>
      Pretty.char '}'
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
      (prettyExp names a)
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
      (prettyExp names a)
    App a b ->
      (case a of
         Abs{} -> Pretty.parens
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         Case{} -> Pretty.parens
         _ -> id)
      (prettyExp names a) <>
      Pretty.space <>
      (case b of
         Thunk{} -> Pretty.parens
         Ctor _ (_:_) -> Pretty.parens
         _ -> id)
      (prettyExp names b)

prettyKind :: Kind -> Doc
prettyKind k =
  case k of
    KArr a b ->
      (case a of
         KArr{} -> Pretty.parens
         _ -> id)
      (prettyKind a) <>
      Pretty.text " -> " <>
      prettyKind b
    KComputation -> Pretty.text "Computation"
    KValue -> Pretty.text "Value"

prettyTy :: (Int -> Maybe Doc) -> Ty -> Doc
prettyTy names ty =
  case ty of
    TName a -> Pretty.text $ Text.unpack a
    TForall name k a ->
      let m_ndoc = Pretty.text . Text.unpack <$> name in
      Pretty.text "forall (" <>
      foldMap (<> Pretty.space) m_ndoc <>
      Pretty.text ": " <>
      prettyKind k <>
      Pretty.text "). " <>
      prettyTy (\case; 0 -> m_ndoc; n -> names (n-1)) a
    TApp (TApp With a) b ->
      (case a of
         TApp (TApp Arrow _) _ -> Pretty.parens
         TForall{} -> Pretty.parens
         _ -> id)
      (prettyTy names a) <>
      Pretty.text " & " <>
      (case b of
         TApp (TApp Arrow _) _ -> Pretty.parens
         TForall{} -> Pretty.parens
         _ -> id)
      (prettyTy names b)
    TApp (TApp Arrow a) b ->
      (case a of
         TApp (TApp Arrow _) _ -> Pretty.parens
         TForall{} -> Pretty.parens
         _ -> id)
      (prettyTy names a) <>
      Pretty.text " -> " <>
      prettyTy names b
    TApp a b ->
      (case a of
         TApp (TApp Arrow _) _ -> Pretty.parens
         TForall{} -> Pretty.parens
         _ -> id)
      (prettyTy names a) <>
      Pretty.space <>
      (case b of
         TApp{} -> Pretty.parens
         TForall{} -> Pretty.parens
         _ -> id)
      (prettyTy names b)
    U -> Pretty.char 'U'
    TInd a -> Pretty.text $ Text.unpack a
    F -> Pretty.char 'F'
    With -> Pretty.text "(&)"
    Arrow -> Pretty.text "(->)"
    TVar a -> fromMaybe (Pretty.char '#' <> Pretty.int a) (names a)
