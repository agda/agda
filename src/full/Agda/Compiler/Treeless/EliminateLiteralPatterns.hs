-- | Converts case matches on literals to if cascades with equality comparisons.
module Agda.Compiler.Treeless.EliminateLiteralPatterns where

import Data.Maybe

import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Treeless
import Agda.Syntax.Literal
import qualified Agda.Syntax.Internal as I

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Substitute

import Agda.Compiler.Treeless.Subst

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
    tr t = case t of
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
      TCase sc t@CaseInfo{caseType = CTData dt} def alts -> TCase sc t (tr def) (map trAlt alts)
        where
          trAlt a = case a of
            TAGuard g b -> TAGuard (tr g) (tr b)
            TACon q a b -> TACon q a (tr b)
            TALit l b   -> TALit l (tr b)
      TCase _ _ _ _ -> __IMPOSSIBLE__

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

    isCaseOn (CTData dt) xs = dt `elem` mapMaybe ($ kit) xs
    isCaseOn _ _ = False

    eqFromLit :: Literal -> TPrim
    eqFromLit x = case x of
      LitNat _ _     -> PEqI
      LitFloat _ _   -> PEqF
      LitString _ _  -> PEqS
      LitChar _ _    -> PEqC
      LitQName _ _   -> PEqQ
      _              -> __IMPOSSIBLE__
