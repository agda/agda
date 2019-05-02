-- | Translates guard alternatives to if-then-else cascades.
--
-- The builtin translation must be run before this transformation.
module Agda.Compiler.Treeless.GuardsToPrims ( convertGuards ) where

import qualified Data.List as List


import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Treeless
import Agda.Syntax.Literal

import Agda.TypeChecking.Substitute

import Agda.Compiler.Treeless.Subst

import Agda.Utils.Impossible




convertGuards :: TTerm -> TTerm
convertGuards = tr
  where
    tr t = case t of
      TCase sc t def alts ->
        if null otherAlts
          then
            def'
          else
            TCase sc t def' (fmap trAlt otherAlts)
        where
          (plusAlts, otherAlts) = splitAlts alts

          guardedAlt :: TAlt -> TTerm -> TTerm
          guardedAlt (TAGuard g body) cont = tIfThenElse (tr g) (tr body) (tr cont)
          guardedAlt _ _ = __IMPOSSIBLE__

          def' = foldr guardedAlt (tr def) plusAlts

          trAlt (TAGuard{}) = __IMPOSSIBLE__
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

      TCoerce a               -> TCoerce (tr a)
      TLam b                  -> TLam (tr b)
      TApp a bs               -> TApp (tr a) (map tr bs)
      TLet e b                -> TLet (tr e) (tr b)

-- | Split alts into TAGuard alts and other alts.
splitAlts :: [TAlt] -> ([TAlt], [TAlt])
splitAlts = List.partition isGuardAlt
  where isGuardAlt (TAGuard _ _) = True
        isGuardAlt _ = False
