{-# OPTIONS_GHC -Wunused-imports #-}

-- | Converts case matches on literals to if cascades with equality comparisons.
module Agda.Compiler.Treeless.EliminateLiteralPatterns where

import Data.Maybe

import Agda.Syntax.Treeless
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Primitive

import Agda.Utils.Impossible


eliminateLiteralPatterns :: TTerm -> TCM TTerm
eliminateLiteralPatterns t = do
  kit <- BuiltinKit <$> getBuiltinName builtinNat <*> getBuiltinName builtinInteger
  return $ transform kit t

data BuiltinKit = BuiltinKit
  { nat :: Maybe QName
  , int :: Maybe QName
  }

transform :: BuiltinKit -> TTerm -> TTerm
transform kit = tr
  where
    tr :: TTerm -> TTerm
    tr = \case
      TCase sc t def alts | caseType t `elem` [CTChar, CTString, CTQName, CTNat, CTInt, CTFloat] ->
        foldr litAlt (tr def) alts
        where
          litAlt :: TAlt -> TTerm -> TTerm
          litAlt (TALit l body) cont =
            tIfThenElse
              (tOp (eqFromLit l) (TLit l) (TVar sc))
              (tr body)
              cont
          litAlt _ _ = __IMPOSSIBLE__
      TCase sc t@CaseInfo{caseType = CTData dt} def alts ->
        TCase sc t (tr def) (map trAlt alts)
        where
          trAlt = \case
            TAGuard g b -> TAGuard (tr g) (tr b)
            TACon q a b -> TACon q a (tr b)
            TALit l b   -> TALit l (tr b)
      TCase _ _ _ _ -> __IMPOSSIBLE__

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

    -- TODO:: Defined but not used
    isCaseOn (CTData dt) xs = dt `elem` mapMaybe ($ kit) xs
    isCaseOn _ _ = False

    eqFromLit :: Literal -> TPrim
    eqFromLit = \case
      LitNat _     -> PEqI
      LitFloat _   -> PEqF
      LitString _  -> PEqS
      LitChar _    -> PEqC
      LitQName _   -> PEqQ
      _ -> __IMPOSSIBLE__
