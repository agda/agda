-- | Eliminates case defaults by adding an alternative for all possible
-- constructors. Literal cases are preserved as-is.
module Agda.Compiler.Treeless.EliminateDefaults where

import Control.Monad
import qualified Data.List as List

import Agda.Syntax.Treeless

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute

import Agda.Compiler.Treeless.Subst () --instance only

eliminateCaseDefaults :: TTerm -> TCM TTerm
eliminateCaseDefaults = tr
  where
    tr :: TTerm -> TCM TTerm
    tr = \case
      TCase sc ct@CaseInfo{caseType = CTData qn} def alts
        | not (isUnreachable def) -> do
        dtCons <- defConstructors . theDef <$> getConstInfo qn
        let missingCons = dtCons List.\\ map aCon alts
        def <- tr def
        newAlts <- forM missingCons $ \con -> do
          Constructor {conArity = ar} <- theDef <$> getConstInfo con
          return $ TACon con ar (TVar ar)

        alts' <- (++ newAlts) <$> mapM (trAlt . raise 1) alts

        return $ TLet def $ TCase (sc + 1) ct tUnreachable alts'
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

    trAlt :: TAlt -> TCM TAlt
    trAlt = \case
      TAGuard g b -> TAGuard <$> tr g <*> tr b
      TACon q a b -> TACon q a <$> tr b
      TALit l b   -> TALit l <$> tr b
