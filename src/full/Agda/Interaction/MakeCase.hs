{-# LANGUAGE CPP #-}

module Agda.Interaction.MakeCase where

import Prelude hiding (mapM, mapM_)
import Control.Applicative
import Control.Monad hiding (mapM, mapM_)
import Control.Monad.State hiding (mapM, mapM_)
import qualified Data.Map as Map
import Data.Traversable
import Data.List

import Agda.Syntax.Common
import Agda.Syntax.Position
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Info as A
import Agda.Syntax.Abstract.Views
import Agda.Syntax.Internal
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Scope.Base (emptyScopeInfo)

import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Context as Context
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecker

import Agda.Interaction.BasicOps

import Agda.Utils.Size
import Agda.Utils.Permutation

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Find the clause whose right hand side is the given meta
-- BY SEARCHING THE WHOLE SIGNATURE. Returns
-- the original clause, before record patterns have been translated
-- away. Raises an error if there is no matching clause.
--
-- Andreas, 2010-09-21: This looks like a SUPER UGLY HACK to me. You are
-- walking through the WHOLE signature to find an information you have
-- thrown away earlier.  (shutter with disgust).
-- This code fails for record rhs because they have been eta-expanded,
-- so the MVar is gone.
findClause :: MetaId -> TCM (QName, Clause)
findClause m = do
  sig <- getImportedSignature
  let res = do
        def <- Map.elems $ sigDefinitions sig
        Function{funClauses = cs} <- [theDef def]
        c <- map originalClause cs
        unless (rhsIsm $ clauseBody c) []
        return (defName def, c)
  case res of
    []  -> do
      reportSDoc "interaction.case" 10 $ vcat $
        [ text "Interaction.MakeCase.findClause fails"
        , text "expected rhs to be meta var" <+> (text $ show m)
        , text "but could not find it in the signature"
        ]
      reportSDoc "interaction.case" 20 $ vcat $ map (text . show) (Map.elems $ sigDefinitions sig)  -- you asked for it!
      typeError $ GenericError "Right hand side must be a single hole when making a case distinction."
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
makeCase hole rng s = withInteractionId hole $ do
  meta        <- lookupInteractionId hole
  (f, clause@(Clause{ clauseTel = tel, clausePerm = perm, clausePats = ps })) <- findClause meta
  reportSDoc "interaction.case" 10 $ vcat
    [ text "splitting clause:"
    , nest 2 $ vcat
      [ text "context =" <+> (prettyTCM =<< getContextTelescope)
      , text "tel     =" <+> prettyTCM tel
      , text "perm    =" <+> text (show perm)
      , text "ps      =" <+> text (show ps)
      ]
    ]
  var         <- deBruijnIndex =<< parseExprIn hole rng s
  z           <- splitClauseWithAbs clause var
  case z of
    Left err        -> typeError . GenericError . show =<< prettySplitError err
    Right (Left cl) -> (:[]) <$> makeAbsurdClause f cl
    Right (Right c) -> mapM (makeAbstractClause f) c

prettySplitError :: SplitError -> TCM Doc
prettySplitError err = case err of
  NotADatatype t -> fsep $
    pwords "Cannot pattern match on non-datatype" ++ [prettyTCM t]
  IrrelevantDatatype t -> fsep $
    pwords "Cannot pattern match on datatype" ++ [prettyTCM t] ++
    pwords "since it is declared irrelevant"
  CoinductiveDatatype t -> fsep $
    pwords "Cannot pattern match on the coinductive type" ++ [prettyTCM t]
  NoRecordConstructor t -> fsep $
    pwords "Cannot pattern match on record" ++ [prettyTCM t] ++
    pwords "because it has no constructor"
  CantSplit c tel cIxs gIxs flex -> addCtxTel tel $ vcat
    [ fsep $ pwords "Cannot pattern match on constructor" ++ [prettyTCM c <> text ","] ++
             pwords "since the inferred indices"
    , nest 2 $ prettyTCM cIxs
    , fsep $ pwords "cannot be unified with the expected indices"
    , nest 2 $ prettyTCM gIxs
    , fsep $ pwords "for some" ++ punctuate comma (map prettyTCM flex)
    ]
  GenericSplitError s -> fsep $
    pwords "Split failed:" ++ pwords s

makeAbsurdClause :: QName -> SplitClause -> TCM A.Clause
makeAbsurdClause f (SClause tel perm ps _) = do
  reportSDoc "interaction.case" 10 $ vcat
    [ text "Interaction.MakeCase.makeCase: split clause:"
    , nest 2 $ vcat
      [ text "context =" <+> (prettyTCM =<< getContextTelescope)
      , text "tel =" <+> prettyTCM tel
      , text "perm =" <+> text (show perm)
      , text "ps =" <+> text (show ps)
      ]
    ]
  withCurrentModule (qnameModule f) $ do
    -- Normalise the dot patterns
    ps <- addCtxTel tel $ normalise ps
    inContext [] $ reify $ NamedClause f $ Clause noRange tel perm ps NoBody

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
  (v, _) <- -- Andreas, 2010-09-21 allow splitting on irrelevant (record) vars
            Context.wakeIrrelevantVars $
              inferExpr e
  case v of
    Var n _ -> return n
    _       -> typeError . GenericError . show =<< (fsep $
                pwords "The scrutinee of a case distinction must be a variable,"
                ++ [ prettyTCM v ] ++ pwords "isn't.")
