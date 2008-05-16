{-# OPTIONS -cpp #-}

module Interaction.MakeCase where

import Prelude hiding (mapM, mapM_)
import Control.Applicative
import Control.Monad hiding (mapM, mapM_)
import Control.Monad.State hiding (mapM, mapM_)
import qualified Data.Map as Map
import Data.Traversable
import Data.List

import Syntax.Common
import Syntax.Position
import qualified Syntax.Abstract as A
import qualified Syntax.Info as A
import Syntax.Abstract.Views
import Syntax.Internal
import Syntax.Translation.InternalToAbstract
import Syntax.Scope.Base (emptyScopeInfo)

import TypeChecking.Monad
import TypeChecking.Coverage
import TypeChecking.Pretty
import TypeChecker

import Interaction.BasicOps

import Utils.Size
import Utils.Permutation

#include "../undefined.h"
import Utils.Impossible

-- | Find the clause whose right hand side is the given meta.
--   Raises an error if there is no such clause.
findClause :: MetaId -> TCM (QName, Clause)
findClause m = do
  sig <- getSignature
  let res = do
        def <- Map.elems $ sigDefinitions sig
        Function{funClauses = cs} <- [theDef def]
        c@(Clause _ _ _ body) <- cs
        unless (rhsIsm body) []
        return (defName def, c)
  case res of
    []  -> fail "Right hand side must be a single hole when making case."
    [r] -> return r
    _   -> __IMPOSSIBLE__
  where
    rhsIsm (Bind b)   = rhsIsm $ absBody b
    rhsIsm (NoBind b) = rhsIsm b
    rhsIsm NoBody     = False
    rhsIsm (Body e)   = case e of
      MetaV m' _  -> m == m'
      _           -> False

makeCase :: InteractionId -> Range -> String -> TCM [A.Clause]
makeCase hole rng s = do
  meta        <- lookupInteractionId hole
  (f, clause) <- findClause meta
  var         <- withInteractionId hole $ deBruijnIndex =<< parseExprIn hole rng s
  z           <- splitClauseWithAbs clause var
  case z of
    Left err        -> fail $ show err
    Right (Left cl) -> (:[]) <$> makeAbsurdClause f cl
    Right (Right c) -> mapM (makeAbstractClause f) c

makeAbsurdClause :: QName -> SplitClause -> TCM A.Clause
makeAbsurdClause f (SClause tel perm ps _) = do
  reportSDoc "interaction.case" 10 $ vcat
    [ text "context =" <+> (prettyTCM =<< getContextTelescope)
    , text "tel =" <+> prettyTCM tel
    , text "perm =" <+> text (show perm)
    , text "ps =" <+> text (show ps)
    ]
  withCurrentModule (qnameModule f) $
    reify $ NamedClause f $ Clause tel perm ps NoBody

makeAbstractClause :: QName -> SplitClause -> TCM A.Clause
makeAbstractClause f cl = do
  A.Clause lhs _ _ <- makeAbsurdClause f cl
  return $ mkClause lhs
  where
    mkClause :: A.LHS -> A.Clause
    mkClause lhs = A.Clause lhs (A.RHS $ A.QuestionMark info) []
      where
        info = A.MetaInfo noRange emptyScopeInfo Nothing

deBruijnIndex :: A.Expr -> TCM Nat
deBruijnIndex e = do
  (v, _) <- inferExpr e
  case v of
    Var n _ -> return n
    _       -> fail $ "Should be a variable: " ++ show v

