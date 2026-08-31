{-# OPTIONS_GHC -Wunused-imports #-}

-- | Eliminates case defaults by adding an alternative for all possible
-- constructors. Literal cases are preserved as-is.
module Agda.Compiler.Treeless.EliminateDefaults where

import Control.Monad
import qualified Data.List as List

import Agda.Syntax.Treeless

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute

import Agda.Compiler.Treeless.Subst () --instance only

-- Eliminate a case default.
-- Leaves its argument unchanged if:
--  * it not a data-type case split.
--  * the default case is unreachable (this makes the function idempotent)
eliminateCaseDefaultAtTopLevelIfPresent :: TTerm -> TCM TTerm
eliminateCaseDefaultAtTopLevelIfPresent (TCase sc ci@CaseInfo{caseType = CTData qn} def alts)
  | not (isUnreachable def) = do
    dtCons <- defConstructors . theDef <$> getConstInfo qn
    let missingCons = dtCons List.\\ map aCon alts
    newAlts <- forM missingCons $ \con -> do
      Constructor {conArity = ar} <- theDef <$> getConstInfo con
      return $ TACon con ar (TVar ar)

    alts' <- (++ newAlts) <$> mapM (trAlt . raise 1) alts

    return $ TLet def $ TCase (sc + 1) ci tUnreachable alts'
eliminateCaseDefaultAtTopLevelIfPresent t = pure t

trAlt :: TAlt -> TCM TAlt
trAlt = \case
  TAGuard g b -> TAGuard <$> eliminateCaseDefaults g <*> eliminateCaseDefaults b
  TACon q a b -> TACon q a <$> eliminateCaseDefaults b
  TALit l b   -> TALit l <$> eliminateCaseDefaults b

eliminateCaseDefaults :: TTerm -> TCM TTerm
eliminateCaseDefaults = tr
  where
    tr :: TTerm -> TCM TTerm
    tr = eliminateCaseDefaultAtTopLevelIfPresent >=> \case
      TCase sc ct def alts -> TCase sc ct <$> tr def <*> mapM trAlt alts

      t@TVar{}    -> return t
      t@TDef{}    -> return t
      t@TCon{}    -> return t
      t@TPrim{}   -> return t
      t@TLit{}    -> return t
      t@TUnit{}   -> return t
      t@TSort{}   -> return t
      t@TErased{} -> return t
      t@TError{}  -> return t

      TCoerce a               -> TCoerce <$> tr a
      TLam b                  -> TLam <$> tr b
      TApp a bs               -> TApp <$> tr a <*> mapM tr bs
      TLet e b                -> TLet <$> tr e <*> tr b

