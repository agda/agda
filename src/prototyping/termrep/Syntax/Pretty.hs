
module Syntax.Pretty where

import Control.Arrow ((***))
import Text.PrettyPrint

import Syntax.Abstract

class Pretty a where
  pretty     :: a -> Doc
  prettyPrec :: Int -> a -> Doc

  pretty       = prettyPrec 0
  prettyPrec _ = pretty

instance Pretty Decl where
  pretty (Def x a t) =
    text x <+> sep [ text ":" <+> pretty a
                   , text "=" <+> pretty t ]
  pretty (Ax x a) = text x <+> text ":" <+> pretty a

instance Pretty Expr where
  prettyPrec n e = case e of
    Pi "_" a b  -> mparens (n > 0) $ sep
                   [ prettyPrec 1 a <+> text "->"
                   , pretty b ]
    Pi x a b    -> mparens (n > 0) $ sep
                   [ parens (hsep [text x, text ":", pretty a]) <+> text "->"
                   , pretty b ]
    Sigma x a b -> mparens (n > 0) $ sep
                   [ parens (hsep [text x, text ":", pretty a]) <+> text "*"
                   , pretty b ]
    Lam{}       -> mparens (n > 0) $ sep
                   [ text "\\" <+> fsep (map text xs) <+> text "->"
                   , nest 2 $ pretty b ]
      where
        (xs, b) = lambdas e
        lambdas (Lam x e) = (x :) *** id $ lambdas e
        lambdas e         = ([], e)
    Let d e     -> mparens (n > 0) $
                   sep [ text "let" <+> pretty d <+> text "in"
                       , pretty e ]
    App s t     -> mparens (n > 1) $ prettyPrec 1 s <+> prettyPrec 2 t
    Meta        -> text "_"
    Var x       -> text x
    Prim x      -> text x

mparens True  = parens
mparens False = id
