{-# LANGUAGE CPP #-}
-- | Converts case matches on literals to if cascades with equality comparisons.
module Agda.Compiler.Treeless.EliminateLiteralPatterns where

import Data.List


import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Treeless
import Agda.Syntax.Literal

import Agda.TypeChecking.Substitute

import Agda.Compiler.Treeless.Subst

import Agda.Utils.Impossible

#include "undefined.h"


eliminateLiteralPatterns :: TTerm -> TTerm
eliminateLiteralPatterns = tr
  where
    tr t = case t of
      TCase sc t@(CTData _) def alts -> TCase sc t (tr def) (map trAlt alts)
        where
          trAlt a = a { aBody = tr (aBody a) }
      TCase sc t def alts ->
        foldr litAlt (tr def) alts
        where
          litAlt :: TAlt -> TTerm -> TTerm
          litAlt (TALit l body) cont =
            tIfThenElse
              (tOp PEq (TLit l) (TVar sc))
              (tr body)
              cont
          litAlt _ _ = __IMPOSSIBLE__

      TVar{}    -> t
      TDef{}    -> t
      TCon{}    -> t
      TPrim{}   -> t
      TLit{}    -> t
      TUnit{}   -> t
      TSort{}   -> t
      TErased{} -> t
      TError{}  -> t

      TLam b                  -> TLam (tr b)
      TApp a bs               -> TApp (tr a) (map tr bs)
      TLet e b                -> TLet (tr e) (tr b)


