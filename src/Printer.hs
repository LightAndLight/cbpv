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

prettyExp :: (Int -> Maybe Doc) -> (Int -> Maybe Doc) -> Exp a -> Doc
prettyExp names tyNames tm =
  case tm of
    Addr{} -> error "Addr"
    AbsTy name k a ->
      let m_ndoc = Pretty.text . Text.unpack <$> name in
      Pretty.text "\\@" <>
      Pretty.parens (foldMap (<> Pretty.space) m_ndoc <> Pretty.text ": " <> prettyKind k) <>
      Pretty.text " -> " <>
      prettyExp names (\case; 0 -> m_ndoc; n -> tyNames (n-1)) a
    AppTy a t ->
      (case a of
         Abs{} -> Pretty.parens
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         Case{} -> Pretty.parens
         CoCase{} -> Pretty.parens
         _ -> id)
      (prettyExp names tyNames a) <>
      Pretty.text " @" <>
      (case t of
         TApp{} -> Pretty.parens
         _ -> id)
      (prettyTy tyNames t)
    Name a -> Pretty.text $ Text.unpack a
    Ann a b ->
      (case a of
         Abs{} -> Pretty.parens
         Case{} -> Pretty.parens
         CoCase{} -> Pretty.parens
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         _ -> id)
      (prettyExp names tyNames a) <>
      Pretty.text " : " <>
      prettyTy tyNames b
    Var a ->
      fromMaybe (Pretty.char '#' <> Pretty.int a) $ names a
    Thunk a ->
      Pretty.text "thunk" <>
      Pretty.brackets (prettyExp names tyNames a)
    Ctor a bs ->
      Pretty.text (Text.unpack a) <>
      Pretty.brackets
        (fold . intersperse (Pretty.text ", ") $ prettyExp names tyNames <$> bs)
    Return a ->
      Pretty.text "return" <>
      Pretty.brackets (prettyExp names tyNames a)
    Abs name a b ->
      let m_ndoc = Pretty.text . Text.unpack <$> name in
      Pretty.text "\\(" <>
      foldMap (<> Pretty.space) m_ndoc <>
      Pretty.text ": " <>
      prettyTy tyNames a <>
      Pretty.text ") -> " <>
      prettyExp (\case; 0 -> m_ndoc; n -> names (n-1)) tyNames b
    Bind name a b ->
      let m_ndoc = Pretty.text . Text.unpack <$> name in
      Pretty.text "bind" <>
      foldMap (\x -> Pretty.space <> x <> Pretty.space) m_ndoc <>
      Pretty.text "= " <>
      (case a of
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         _ -> id)
      (prettyExp names tyNames a) <>
      Pretty.text " in " <>
      prettyExp (\case; 0 -> m_ndoc; n -> names (n-1)) tyNames b
    Let name a b ->
      let m_ndoc = Pretty.text . Text.unpack <$> name in
      Pretty.text "let" <>
      foldMap (\x -> Pretty.space <> x <> Pretty.space) m_ndoc <>
      Pretty.text "= " <>
      prettyExp names tyNames a <>
      Pretty.text " in" Pretty.<$>
      prettyExp (\case; 0 -> m_ndoc; n -> names (n-1)) tyNames b
    Fix name t a ->
      let m_ndoc = Pretty.text . Text.unpack <$> name in
      Pretty.text "fix " <>
      fromMaybe (Pretty.text "<unnamed>") m_ndoc <>
      Pretty.text " : " <> prettyTy tyNames t <>
      Pretty.text " in " <>
      prettyExp (\case; 0 -> m_ndoc; n -> names (n-1)) tyNames a
    Force a ->
      Pretty.text "force" <>
      Pretty.brackets (prettyExp names tyNames a)
    Case a bs ->
      Pretty.text "case " <>
      prettyExp names tyNames a <>
      Pretty.text " of {" Pretty.<$>
      Pretty.indent 2
        (fold . intersperse (Pretty.char ';' <> Pretty.hardline) .
         NonEmpty.toList $
         (\(Branch p e) ->
            let arity = patArity p in
            prettyPat p <>
            Pretty.text " -> " <>
            prettyExp
              (\n ->
                 if n < arity
                 then Just $ fmap (Pretty.text . Text.unpack) (patNames p) !! n
                 else names (n-arity))
              tyNames
              e) <$> bs) Pretty.<$>
      Pretty.char '}'
    Dtor a args b ->
      (case b of
         App{} -> Pretty.parens
         Abs{} -> Pretty.parens
         Let{} -> Pretty.parens
         Bind{} -> Pretty.parens
         Case{} -> Pretty.parens
         CoCase{} -> Pretty.parens
         _ -> id)
      (prettyExp names tyNames b) <>
      Pretty.dot <>
      Pretty.text (Text.unpack a) <>
      Pretty.brackets
        (fold . intersperse (Pretty.text ", ") $
         prettyExp names tyNames <$> args)
    CoCase a bs ->
      Pretty.text "cocase " <>
      prettyTy tyNames a <>
      Pretty.text " of {" Pretty.<$>
      Pretty.indent 2
        (Pretty.vsep . NonEmpty.toList $
         (\(CoBranch d arity tys names' e) ->
            Pretty.text (Text.unpack d) <>
            Pretty.brackets
              (fold . intersperse (Pretty.text ", ") $
               (\(n, t) ->
                  Pretty.hsep
                  [ Pretty.text $ Text.unpack n
                  , Pretty.char ':'
                  , prettyTy names t
                  ]) <$>
                zip names' tys) <>
            Pretty.text " -> " <>
            prettyExp
              (\n ->
                 if n < arity
                 then Just . Pretty.text . Text.unpack $ names' !! n
                 else names (n-arity))
              tyNames
              e) <$>
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
      (prettyExp names tyNames a) <>
      Pretty.space <>
      (case b of
         Let{} -> Pretty.parens
         Case{} -> Pretty.parens
         _ -> id)
      (prettyExp names tyNames b)

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
