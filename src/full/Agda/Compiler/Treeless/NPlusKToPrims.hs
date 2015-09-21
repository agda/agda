-- | Translates NPlusK alternatives to if-then-else cascades.
--
-- The NPlusK optimization must be run before this transformation.
{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.NPlusKToPrims
  ( convertNPlusK )
where

import Data.List


import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Treeless
import Agda.Syntax.Literal

import Agda.TypeChecking.Substitute

import Agda.Compiler.Treeless.Subst

import Agda.Utils.Impossible

#include "undefined.h"



convertNPlusK :: TTerm -> TTerm
convertNPlusK = tr
  where
    tr t = case t of
      TCase sc t def alts -> TCase sc t def' (fmap trAlt otherAlts)
        where
          (plusAlts, otherAlts) = splitAlts alts

          guardedAlt :: TAlt -> TTerm -> TTerm
          guardedAlt (TAPlus{aSucs = k, aBody = body}) cont =
            TApp (TPrim PIfThenElse)
              [ TApp (TPrim PGreaterOrEqual) [TVar sc, tInt k]
              , TLet (tOp PSub (TVar sc) (tInt k)) (tr body)
              , cont
              ]
          guardedAlt _ _ = __IMPOSSIBLE__

          def' = foldr guardedAlt (tr def) plusAlts

          trAlt (TAPlus{}) = __IMPOSSIBLE__
          trAlt a = a { aBody = tr (aBody a) }

      TVar{}    -> t
      TDef{}    -> t
      TCon{}    -> t
      TPrim{}   -> t
      TLit{}    -> t
      TUnit{}   -> t
      TSort{}   -> t
      TErased{} -> t
      TError{}  -> t

      TPi (TType a) (TType b) -> TPi (TType $ tr a) (TType $ tr b)
      TLam b                  -> TLam (tr b)
      TApp a bs               -> TApp (tr a) (map tr bs)
      TLet e b                -> TLet (tr e) (tr b)

-- | Split alts into TAPlus alts and other alts.
splitAlts :: [TAlt] -> ([TAlt], [TAlt])
splitAlts = partition isPlusAlt
  where isPlusAlt (TAPlus _ _) = True
        isPlusAlt _ = False
