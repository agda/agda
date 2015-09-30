{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE TupleSections #-}

module Agda.Interaction.MakeCase where

import Prelude hiding (mapM, mapM_, null)
import Control.Applicative hiding (empty)
import Control.Monad hiding (mapM, mapM_, forM)
import Data.Maybe
import Data.Traversable

import Agda.Syntax.Common
import Agda.Syntax.Position
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Info as A
import Agda.Syntax.Internal
import Agda.Syntax.Scope.Monad (resolveName, ResolvedName(..))
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Translation.InternalToAbstract

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.RecordPatterns
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Rules.LHS.Implicit
import Agda.TheTypeChecker

import Agda.Interaction.Options
import Agda.Interaction.BasicOps

import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Null
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Singleton
import Agda.Utils.Size
import qualified Agda.Utils.HashMap as HMap

#include "undefined.h"
import Agda.Utils.Impossible

type CaseContext = Maybe ExtLamInfo

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
findClause :: MetaId -> TCM (CaseContext, QName, Clause)
findClause m = do
  sig <- getImportedSignature
  let res = do
        def <- HMap.elems $ sigDefinitions sig
        Function{funClauses = cs, funExtLam = extlam} <- [theDef def]
        c <- cs
        unless (rhsIsm $ clauseBody c) []
        return (extlam, defName def, c)
  case res of
    []  -> do
      reportSDoc "interaction.case" 10 $ vcat $
        [ text "Interaction.MakeCase.findClause fails"
        , text "expected rhs to be meta var" <+> (text $ show m)
        , text "but could not find it in the signature"
        ]
      reportSDoc "interaction.case" 100 $ vcat $ map (text . show) (HMap.elems $ sigDefinitions sig)  -- you asked for it!
      ifM (isInstantiatedMeta m)
        -- Andreas, 2012-03-22 If the goal has been solved by eta expansion, further
        -- case splitting is pointless and `smart-ass Agda' will refuse.
        -- Maybe not the best solution, but the lazy alternative to replace this
        -- SUPER UGLY HACK.
        (typeError $ GenericError "Since goal is solved, further case distinction is not supported; try `Solve constraints' instead")
        (typeError $ GenericError "Right hand side must be a single hole when making a case distinction")
    [triple] -> return triple
    _   -> __IMPOSSIBLE__
  where
    rhsIsm (Bind b)   = rhsIsm $ unAbs b
    rhsIsm NoBody     = False
    rhsIsm (Body e)   = case ignoreSharing e of
      MetaV m' _  -> m == m'
      _           -> False


-- | Parse variables (visible or hidden), returning their de Bruijn indices.
--   Used in 'makeCase'.

parseVariables :: InteractionId -> Range -> [String] -> TCM [Int]
parseVariables ii rng ss = do

  -- Get into the context of the meta.
  mId <- lookupInteractionId ii
  updateMetaVarRange mId rng
  mi  <- getMetaInfo <$> lookupMeta mId
  enterClosure mi $ \ r -> do

    -- Get printed representation of variables in context.
    n  <- getContextSize
    xs <- forM (downFrom n) $ \ i -> do
      (,i) . P.render <$> prettyTCM (var i)

    -- Get number of module parameters.  These cannot be split on.
    fv <- getModuleFreeVars =<< currentModule
    let numSplittableVars = n - fv

    -- Resolve each string to a variable.
    forM ss $ \ s -> do
      let failNotVar = typeError $ GenericError $ "Not a (splittable) variable: " ++ s
          done i
            | i < numSplittableVars = return i
            | otherwise             = failNotVar

      -- Note: the range in the concrete name is only approximate.
      resName <- resolveName $ C.QName $ C.Name r $ C.stringNameParts s
      case resName of

        -- Fail if s is a name, but not of a variable.
        DefinedName{}       -> failNotVar
        FieldName{}         -> failNotVar
        ConstructorName{}   -> failNotVar
        PatternSynResName{} -> failNotVar

        -- If s is a variable name in scope, get its de Bruijn index
        -- via the type checker.
        VarName x -> do
          (v, _) <- getVarInfo x
          case ignoreSharing v of
            Var i [] -> done i
            _        -> failNotVar

        -- If s is not a name, compare it to the printed variable representation.
        -- This fallback is to enable splitting on hidden variables.
        UnknownName -> do
          case filter ((s ==) . fst) xs of
            []      -> typeError $ GenericError $ "Unbound variable " ++ s
            [(_,i)] -> done i
            -- Issue 1325: Variable names in context can be ambiguous.
            _       -> typeError $ GenericError $ "Ambiguous variable " ++ s


-- | Entry point for case splitting tactic.
makeCase :: InteractionId -> Range -> String -> TCM (CaseContext , [A.Clause])
makeCase hole rng s = withInteractionId hole $ do
  meta <- lookupInteractionId hole
  (casectxt, f, clause@(Clause{ clauseTel = tel, clausePerm = perm, namedClausePats = ps })) <- findClause meta
  reportSDoc "interaction.case" 10 $ vcat
    [ text "splitting clause:"
    , nest 2 $ vcat
      [ text "f       =" <+> prettyTCM f
      , text "context =" <+> (prettyTCM =<< getContextTelescope)
      , text "tel     =" <+> prettyTCM tel
      , text "perm    =" <+> text (show perm)
      , text "ps      =" <+> text (show ps)
      ]
    ]
  let vars = words s
  if null vars then do
    -- split result
    (piTel, sc) <- fixTarget $ clauseToSplitClause clause
    -- Andreas, 2015-05-05 If we introduced new function arguments
    -- do not split on result.  This might be more what the user wants.
    -- To split on result, he can then C-c C-c again.
    -- Andreas, 2015-05-21 Issue 1516:  However, if only hidden
    -- arguments are introduced, C-c C-c virtually does nothing
    -- (as they are not shown and get lost on the way to emacs and back).
    newPats <- if null piTel then return False else do
      -- If there were any pattern introduce, they will only have effect
      -- if any of them is shown by the printer
      imp <- optShowImplicit <$> pragmaOptions
      return $ imp || any visible (telToList piTel)
    scs <- if newPats then return [sc] else do
      res <- splitResult f sc
      case res of
        Nothing  -> typeError $ GenericError $ "Cannot split on result here"
        Just cov -> ifNotM (optCopatterns <$> pragmaOptions) failNoCop $ {-else-} do
          mapM (snd <.> fixTarget) $ splitClauses cov
    (casectxt,) <$> mapM (makeAbstractClause f) scs
  else do
    -- split on variables
    vars <- parseVariables hole rng vars
    (casectxt,) <$> do split f vars $ clauseToSplitClause clause
  where

  failNoCop = typeError $ GenericError $
    "OPTION --copatterns needed to split on result here"

  split :: QName -> [Nat] -> SplitClause -> TCM [A.Clause]
  split f [] clause = singleton <$> makeAbstractClause f clause
  split f (var : vars) clause = do
    z <- splitClauseWithAbsurd clause var
    case z of
      Left err          -> typeError $ SplitError err
      Right (Left cl)   -> (:[]) <$> makeAbsurdClause f cl
      Right (Right cov)
        | null vars -> mapM (makeAbstractClause f) $ splitClauses cov
        | otherwise -> concat <$> do
            forM (splitClauses cov) $ \ cl ->
              split f (mapMaybe (newVar cl) vars) cl

  -- Finds the new variable corresponding to an old one, if any.
  newVar :: SplitClause -> Nat -> Maybe Nat
  newVar c x = case ignoreSharing $ applySubst (scSubst c) (var x) of
    Var y [] -> Just y
    _        -> Nothing


makeAbsurdClause :: QName -> SplitClause -> TCM A.Clause
makeAbsurdClause f (SClause tel perm ps _ t) = do
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
    -- Andreas, 2015-05-29 Issue 635
    -- Contract implicit record patterns before printing.
    c <- translateRecordPatterns $ Clause noRange tel perm ps NoBody t False
    -- Normalise the dot patterns
    ps <- addCtxTel tel $ normalise $ namedClausePats c
    inTopContext $ reify $ QNamed f $ c { namedClausePats = ps }

-- | Make a clause with a question mark as rhs.
makeAbstractClause :: QName -> SplitClause -> TCM A.Clause
makeAbstractClause f cl = do
  A.Clause lhs _ _ _ <- makeAbsurdClause f cl
  let ii = __IMPOSSIBLE__  -- No interaction point since we never type check this
  let info = A.emptyMetaInfo -- metaNumber = Nothing in order to print as ?, not ?n
  return $ A.Clause lhs (A.RHS $ A.QuestionMark info ii) [] False

deBruijnIndex :: A.Expr -> TCM Nat
deBruijnIndex e = do
  (v, _) <- -- Andreas, 2010-09-21 allow splitting on irrelevant (record) vars
--            Context.wakeIrrelevantVars $
            applyRelevanceToContext Irrelevant $
              inferExpr e
  case ignoreSharing v of
    Var n _ -> return n
    _       -> typeError . GenericError . show =<< (fsep $
                pwords "The scrutinee of a case distinction must be a variable,"
                ++ [ prettyTCM v ] ++ pwords "isn't.")
