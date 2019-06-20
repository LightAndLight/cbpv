{-# language GADTs #-}
{-# language LambdaCase #-}
module Printer where

import Data.Foldable (fold)
import Data.List (intersperse)
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
  Pretty.brackets
    (fold . intersperse (Pretty.text ", ") $
     Pretty.text . Text.unpack <$> patNames p)

prettyExp :: (Int -> Maybe Doc) -> Exp a -> Doc
prettyExp names tm =
  case tm of
    Name a -> Pretty.text $ Text.unpack a
    Ann a b ->
      (case a of
         Abs{} -> Pretty.parens
         Case{} -> Pretty.parens
         CoCase{} -> Pretty.parens
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         _ -> id)
      (prettyExp names a) <>
      Pretty.text " : " <>
      prettyTy (const Nothing) b
    Var a ->
      fromMaybe (Pretty.char '#' <> Pretty.int a) $ names a
    Thunk a ->
      Pretty.text "thunk" <>
      Pretty.brackets (prettyExp names a)
    Ctor a bs ->
      Pretty.text (Text.unpack a) <>
      Pretty.brackets
        (fold . intersperse (Pretty.text ", ") $ prettyExp names <$> bs)
    Return a ->
      Pretty.text "return" <>
      Pretty.brackets (prettyExp names a)
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
    Fix a ->
      Pretty.text "fix" <>
      Pretty.brackets (prettyExp names a)
    Force a ->
      Pretty.text "force" <>
      Pretty.brackets (prettyExp names a)
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
    Dtor a b ->
      (case b of
         App{} -> Pretty.parens
         Abs{} -> Pretty.parens
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         Case{} -> Pretty.parens
         CoCase{} -> Pretty.parens
         _ -> id)
      (prettyExp names b) <>
      Pretty.dot <>
      Pretty.text (Text.unpack a)
    CoCase a bs ->
      Pretty.text "cocase " <>
      prettyTy (const Nothing) a <>
      Pretty.text " of {" Pretty.<$>
      Pretty.indent 2
        (Pretty.vsep . NonEmpty.toList $
         (\(CoBranch d e) ->
            Pretty.text (Text.unpack d) <>
            Pretty.text " -> " <>
            prettyExp names e) <$>
          bs) Pretty.<$>
      Pretty.char '}'
    App a b ->
      (case a of
         Abs{} -> Pretty.parens
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         Case{} -> Pretty.parens
         CoCase{} -> Pretty.parens
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
    KComp -> Pretty.text "Comp"
    KVal -> Pretty.text "Val"

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
    TCtor a -> Pretty.text $ Text.unpack a
    F -> Pretty.char 'F'
    Arrow -> Pretty.text "(->)"
    TVar a -> fromMaybe (Pretty.char '#' <> Pretty.int a) (names a)
