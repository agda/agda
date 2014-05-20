{-# OPTIONS_GHC -w -fwarn-incomplete-patterns -Werror #-}
module Syntax.Abstract.Pretty () where

import           Control.Arrow                    ((***))
import           Text.PrettyPrint.Extended

import           Syntax.Abstract

instance Show Name    where showsPrec = defaultShow
instance Show Decl    where showsPrec = defaultShow
instance Show TypeSig where showsPrec = defaultShow
instance Show Expr    where showsPrec = defaultShow
instance Show Head    where showsPrec = defaultShow
instance Show Pattern where showsPrec = defaultShow

instance Show Elim where
  showsPrec p (Apply e) = showParen (p > 0) $ showString "$ " . shows e
  showsPrec _ (Proj x) = showString "." . shows x

instance Pretty Elim where
  pretty = text . show

instance Pretty Name where
  pretty (Name _ x) = text x

instance Pretty TypeSig where
  pretty (Sig x e) =
    sep [ pretty x <+> text ":"
        , nest 2 $ pretty e ]

instance Pretty Decl where
  pretty d = case d of
    TypeSig sig -> pretty sig
    FunDef f ps e ->
      sep [ pretty f <+> fsep (map (prettyPrec 10) ps)
          , nest 2 $ text "=" <+> pretty e ]
    DataDef d xs cs ->
      vcat [ text "data" <+> pretty d <+> fsep (map pretty xs) <+> text "where"
           , nest 2 $ vcat $ map pretty cs ]
    RecDef r xs con fs ->
      vcat [ text "record" <+> pretty r <+> fsep (map pretty xs) <+> text "where"
           , nest 2 $ vcat [ text "constructor" <+> pretty con
                           , sep [ text "field"
                                 , nest 2 $ vcat $ map pretty fs ] ] ]

instance Pretty Expr where
  prettyPrec p e = case e of
    Set _       -> text "Set"
    Meta _      -> text "_"
    Equal (Meta _) x y ->
      condParens (p > 2) $
        sep [ prettyPrec 3 x <+> text "=="
            , nest 2 $ prettyPrec 2 y ]
    Equal a x y -> prettyApp p (text "_==_") [a, x, y]
    Fun a b ->
      condParens (p > 0) $
        sep [ prettyPrec 1 a <+> text "->"
            , pretty b ]
    Pi{} ->
      condParens (p > 0) $
        sep [ prettyTel tel <+> text "->"
            , nest 2 $ pretty b ]
      where
        (tel, b) = piView e
        piView (Pi x a b) = ((x, a) :) *** id $ piView b
        piView a          = ([], a)
    Lam{} ->
      condParens (p > 0) $
      sep [ text "\\" <+> fsep (map pretty xs) <+> text "->"
          , nest 2 $ pretty b ]
      where
        (xs, b) = lamView e
        lamView (Lam x b) = (x :) *** id $ lamView b
        lamView e         = ([], e)
    App{} -> prettyApp p (pretty h) es
      where
        (h, es) = appView e
        appView (App h es) = buildApp h [] es
        appView e = error $ "impossible: pretty application"

        buildApp :: Head -> [Expr] -> [Elim] -> (Head, [Expr])
        buildApp h es0 (Apply e : es1) = buildApp h (es0 ++ [e]) es1
        buildApp h es0 (Proj f  : es1) = buildApp (Def f) [App h $ map Apply es0] es1
        buildApp h es []               = (h, es)

instance Pretty Head where
  pretty h = case h of
    Var x  -> pretty x
    Def f  -> pretty f
    Con c  -> pretty c
    J _    -> text "J"
    Refl _ -> text "refl"

instance Pretty Pattern where
  prettyPrec p e = case e of
    WildP _ -> text "_"
    VarP x  -> pretty x
    ConP c es -> prettyApp p (pretty c) es

prettyTel :: [(Name, Expr)] -> Doc
prettyTel bs = fsep (map pr bs)
  where
    pr (x, e) = parens (pretty x <+> text ":" <+> pretty e)
