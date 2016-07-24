{-# LANGUAGE CPP #-}
-- | Converts case matches on literals to if cascades with equality comparisons.
module Agda.Compiler.Treeless.EliminateLiteralPatterns where

import Data.List


import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Treeless
import Agda.Syntax.Literal
import qualified Agda.Syntax.Internal as I

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Substitute

import Agda.Compiler.Treeless.Subst

import Agda.Utils.Impossible

#include "undefined.h"


eliminateLiteralPatterns :: TTerm -> TCM TTerm
eliminateLiteralPatterns t = do
  nat <- getBuiltin' builtinNat >>= \d -> case d of
    Just (I.Def dt _) -> pure $ Just $ CTData dt
    _ -> pure Nothing
  return $ tr nat t
  where
    tr :: Maybe CaseType -> TTerm -> TTerm
    tr nat t = case t of
      TCase sc t def alts | t `elem` [CTChar, CTString, CTQName] || Just t == nat ->
        foldr litAlt (tr nat def) alts
        where
          litAlt :: TAlt -> TTerm -> TTerm
          litAlt (TALit l body) cont =
            tIfThenElse
              (tOp PEq (TLit l) (TVar sc))
              (tr nat body)
              cont
          litAlt _ _ = __IMPOSSIBLE__
      TCase sc t@(CTData dt) def alts -> TCase sc t (tr nat def) (map trAlt alts)
        where
          trAlt a = a { aBody = tr nat (aBody a) }
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

      TLam b                  -> TLam (tr nat b)
      TApp a bs               -> TApp (tr nat a) (map (tr nat) bs)
      TLet e b                -> TLet (tr nat e) (tr nat b)


