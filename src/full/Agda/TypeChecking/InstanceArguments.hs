{-# LANGUAGE CPP #-}

module Agda.TypeChecking.InstanceArguments where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.Map as Map
import Data.List as List

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Internal

import Agda.TypeChecking.Implicit (implicitArgs)
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce

import {-# SOURCE #-} Agda.TypeChecking.Constraints
import {-# SOURCE #-} Agda.TypeChecking.Rules.Term (checkArguments)
import {-# SOURCE #-} Agda.TypeChecking.MetaVars
import {-# SOURCE #-} Agda.TypeChecking.Conversion

import Agda.Utils.Monad

#include "../undefined.h"
import Agda.Utils.Impossible

initialIFSCandidates :: TCM [(Term, Type)]
initialIFSCandidates = do
  cands1 <- getContextVars
  cands2 <- getScopeDefs
  return $ cands1 ++ cands2
  where
    -- get a list of variables with their type, relative to current context
    getContextVars :: TCM [(Term, Type)]
    getContextVars = do
      ctx <- getContext
      let vars = [ (var i, raise (i + 1) t)
                 | (Dom h r (x, t), i) <- zip ctx [0..], not (unusableRelevance r)
                 ]
      -- get let bindings
      env <- asks envLetBindings
      env <- mapM (getOpen . snd) $ Map.toList env
      let lets = [ (v,t) | (v, Dom h r t) <- env, not (unusableRelevance r) ]
      return $ vars ++ lets

    getScopeDefs :: TCM [(Term, Type)]
    getScopeDefs = do
      scopeInfo <- gets stScope
      let ns = everythingInScope scopeInfo
      let nsList = Map.toList $ nsNames ns
      -- all abstract names in scope are candidates
      -- (even ones that you can't refer to unambiguously)
      let qs = List.map anameName $ snd =<< nsList
      rel   <- asks envRelevance
      cands <- mapM (candidate rel) qs
      return $ concat cands

    candidate :: Relevance -> QName -> TCM [(Term, Type)]
    candidate rel q =
      -- Andreas, 2012-07-07:
      -- we try to get the info for q
      -- while opening a module, q may be in scope but not in the signature
      -- in this case, we just ignore q (issue 674)
      flip catchError handle $ do
        def <- getConstInfo q
        let r = defRelevance def
        if not (r `moreRelevant` rel) then return [] else do
          t   <- defType <$> instantiateDef def
          args <- freeVarsToApply q
          let vs = case theDef def of
               -- drop parameters if it's a projection function...
               Function{ funProjection = Just (_,i) } -> genericDrop (i - 1) args
               _                                      -> args
          return [(Def q vs, t)]
      where
        -- unbound constant throws an internal error
        handle (TypeError _ (Closure {clValue = InternalError _})) = return []
        handle err                                                 = throwError err

{- OLD CODE
    getScopeDefs :: TCM [(Term, Type)]
    getScopeDefs = do
      scopeInfo <- gets stScope
      let ns = everythingInScope scopeInfo
      let nsList = Map.toList $ nsNames ns
      -- all abstract names in scope are candidates
      -- (even ones that you can't refer to unambiguously)
      let cands2Names = nsList >>= snd
      cands2Types <- mapM (typeOfConst . anameName) cands2Names
      cands2Rel   <- mapM (relOfConst . anameName) cands2Names
      cands2FV    <- mapM (constrFreeVarsToApply . anameName) cands2Names
      rel         <- asks envRelevance
      return $ [(Def (anameName an) vs, t) |
                    (an, t, r, vs) <- zip4 cands2Names cands2Types cands2Rel cands2FV,
                    r `moreRelevant` rel ]
    constrFreeVarsToApply :: QName -> TCM Args
    constrFreeVarsToApply n = do
      args <- freeVarsToApply n
      defn <- theDef <$> getConstInfo n
      return $ case defn of
        -- drop parameters if it's a projection function...
        Function{ funProjection = Just (rn,i) } -> genericDrop (i - 1) args
        _                                       -> args
-}

-- | @initializeIFSMeta s t@ generates an instance meta of type @t@
--   with suggested name @s@.
initializeIFSMeta :: String -> Type -> TCM Term
initializeIFSMeta s t = do
  cands <- initialIFSCandidates
  newIFSMeta s t cands

-- | @findInScope m (v,a)s@ tries to instantiate on of the types @a@s
--   of the candidate terms @v@s to the type @t@ of the metavariable @m@.
--   If successful, meta @m@ is solved with the instantiation of @v@.
--   If unsuccessful, the constraint is regenerated, with possibly reduced
--   candidate set.
findInScope :: MetaId -> [(Term, Type)] -> TCM ()
findInScope m cands = whenJustM (findInScope' m cands) $ addConstraint . FindInScope m
{- SAME CODE, POINTFULL
  do fisres <- findInScope' m cands
     case fisres of
       Nothing -> return ()
       Just cs -> addConstraint $ FindInScope m cs
-}

-- Result says whether we need to add constraint, and if so, the set of
-- remaining candidates
findInScope' :: MetaId -> [(Term, Type)] -> TCM (Maybe [(Term, Type)])
findInScope' m cands = ifM (isFrozen m) (return (Just cands)) $ do
    reportSDoc "tc.constr.findInScope" 15 $ text ("findInScope 2: constraint: " ++ show m ++ "; candidates left: " ++ show (length cands))
    t <- getMetaTypeInContext m
    reportSDoc "tc.constr.findInScope" 15 $ text "findInScope 3: t =" <+> prettyTCM t
    reportSLn "tc.constr.findInScope" 70 $ "findInScope 3: t: " ++ show t
    mv <- lookupMeta m
    cands <- checkCandidates m t cands
    reportSLn "tc.constr.findInScope" 15 $ "findInScope 4: cands left: " ++ show (length cands)
    case cands of

      [] -> do
        reportSDoc "tc.constr.findInScope" 15 $ text "findInScope 5: not a single candidate found..."
        typeError $ IFSNoCandidateInScope t

      [(term, t')] -> do
        reportSDoc "tc.constr.findInScope" 15 $ text (
          "findInScope 5: one candidate found for type '") <+>
          prettyTCM t <+> text "': '" <+> prettyTCM term <+>
          text "', of type '" <+> prettyTCM t' <+> text "'."

        ca <- liftTCM $ runErrorT $ checkArguments ExpandLast DontExpandInstanceArguments (getRange mv) [] t' t
        case ca of
          Left _ -> __IMPOSSIBLE__
          Right (args, t'') -> do
{- TODO
        (args, t'') <- implicitArgs (...) t'
        do
-}
            leqType t'' t
            ctxArgs <- getContextArgs
            v <- (`applyDroppingParameters` args) =<< reduce term
            assignV m ctxArgs v
            reportSDoc "tc.constr.findInScope" 10 $
              text "solved by instance search:" <+> prettyTCM m
              <+> text ":=" <+> prettyTCM v
            return Nothing

      cs -> do
        reportSDoc "tc.constr.findInScope" 15 $
          text ("findInScope 5: more than one candidate found: ") <+>
          prettyTCM (List.map fst cs)
        return (Just cs)

-- return the meta's type, applied to the current context
getMetaTypeInContext :: MetaId -> TCM Type
getMetaTypeInContext m = do
  mv <- lookupMeta m
  let j = mvJudgement mv
  tj <- getMetaType m
  ctxArgs <- getContextArgs
  normalise $ tj `piApply` ctxArgs

-- returns a refined list of valid candidates and the (normalised) type of the
-- meta, applied to the context (for convenience)
checkCandidates :: MetaId -> Type -> [(Term, Type)] -> TCM [(Term, Type)]
checkCandidates m t cands = localState $ disableDestructiveUpdate $ do
  -- for candidate checking, we don't take into account other IFS
  -- constrains
  dropConstraints (isIFSConstraint . clValue . theConstraint)
  filterM (uncurry $ checkCandidateForMeta m t) cands
  where
    checkCandidateForMeta :: MetaId -> Type -> Term -> Type -> TCM Bool
    checkCandidateForMeta m t term t' =
      verboseBracket "tc.constr.findInScope" 20 ("checkCandidateForMeta " ++ show m) $ do
      liftTCM $ flip catchError handle $ do
        reportSLn "tc.constr.findInScope" 70 $ "  t: " ++ show t ++ "\n  t':" ++ show t' ++ "\n  term: " ++ show term ++ "."
        reportSDoc "tc.constr.findInScope" 20 $ vcat
          [ text "checkCandidateForMeta"
          , text "t    =" <+> prettyTCM t
          , text "t'   =" <+> prettyTCM t'
          , text "term =" <+> prettyTCM term
          ]
        localState $ do
           -- domi: we assume that nothing below performs direct IO (except
           -- for logging and such, I guess)
          ca <- runErrorT $ checkArguments ExpandLast DontExpandInstanceArguments  noRange [] t' t
          case ca of
            Left _ -> return False
            Right (args, t'') -> do
              reportSDoc "tc.constr.findInScope" 20 $
                text "instance search: checking" <+> prettyTCM t''
                <+> text "<=" <+> prettyTCM t
              -- if constraints remain, we abort, but keep the candidate
              flip (ifNoConstraints_ $ leqType t'' t) (const $ return True) $ do
              --tel <- getContextTelescope
              ctxArgs <- getContextArgs
              v <- (`applyDroppingParameters` args) =<< reduce term
              reportSDoc "tc.constr.findInScope" 10 $
                text "instance search: attempting" <+> prettyTCM m
                <+> text ":=" <+> prettyTCM v
              assign m ctxArgs v
--              assign m ctxArgs (term `apply` args)
              -- make a pass over constraints, to detect cases where some are made
              -- unsolvable by the assignment, but don't do this for FindInScope's
              -- to prevent loops. We currently also ignore UnBlock constraints
              -- to be on the safe side.
              solveAwakeConstraints' True
              return True
      where
        handle err = do
          reportSDoc "tc.constr.findInScope" 50 $ text "assignment failed:" <+> prettyTCM err
          return False
    isIFSConstraint :: Constraint -> Bool
    isIFSConstraint FindInScope{} = True
    isIFSConstraint UnBlock{}     = True -- otherwise test/fail/Issue723 loops
    isIFSConstraint _             = False

-- | To preserve the invariant that a constructor is not applied to its
--   parameter arguments, we explicitly check whether function term
--   we are applying to arguments is a unapplied constructor.
--   In this case we drop the first 'conPars' arguments.
--   See Issue670a.
applyDroppingParameters :: Term -> Args -> TCM Term
applyDroppingParameters t vs =
  case ignoreSharing t of
    Con c [] -> do
      def <- theDef <$> getConstInfo c
      case def of
        Constructor {conPars = n} -> return $ Con c (genericDrop n vs)
        _ -> __IMPOSSIBLE__
    _ -> return $ t `apply` vs

-- | Attempt to solve irrelevant metas by instance search.
solveIrrelevantMetas :: TCM ()
solveIrrelevantMetas = mapM_ solveMetaIfIrrelevant =<< getOpenMetas

solveMetaIfIrrelevant :: MetaId -> TCM ()
solveMetaIfIrrelevant x = do
  m <- lookupMeta x
  when (irrelevantOrUnused (getMetaRelevance m)) $ do
    reportSDoc "tc.conv.irr" 20 $ sep
      [ text "instance search for solution of irrelevant meta"
      , prettyTCM x, colon, prettyTCM $ jMetaType $ mvJudgement m
      ]
    flip catchError (const $ return ()) $ do
      findInScope' x =<< initialIFSCandidates
      -- do not add constraints!
      return ()
