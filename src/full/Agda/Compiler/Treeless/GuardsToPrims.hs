{-# OPTIONS_GHC -Wunused-imports #-}

-- | Translates guard alternatives to if-then-else cascades.
--
-- The builtin translation must be run before this transformation.
module Agda.Compiler.Treeless.GuardsToPrims ( convertGuards ) where

import qualified Data.List as List

import Agda.Syntax.Treeless

import Agda.Utils.Impossible


convertGuards :: TTerm -> TTerm
convertGuards = tr
  where
    tr = \case
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

      t@TVar{}    -> t
      t@TDef{}    -> t
      t@TCon{}    -> t
      t@TPrim{}   -> t
      t@TLit{}    -> t
      t@TUnit{}   -> t
      t@TSort{}   -> t
      t@TErased{} -> t
      t@TError{}  -> t

      TCoerce a               -> TCoerce (tr a)
      TLam b                  -> TLam (tr b)
      TApp a bs               -> TApp (tr a) (map tr bs)
      TLet e b                -> TLet (tr e) (tr b)

-- | Split alts into TAGuard alts and other alts.
splitAlts :: [TAlt] -> ([TAlt], [TAlt])
splitAlts = List.partition isGuardAlt
  where isGuardAlt (TAGuard _ _) = True
        isGuardAlt _ = False
