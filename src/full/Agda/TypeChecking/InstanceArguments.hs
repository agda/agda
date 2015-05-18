{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ >= 710
{-# LANGUAGE FlexibleContexts #-}
#endif

module Agda.TypeChecking.InstanceArguments where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as Map
import Data.List as List

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Internal as I

import Agda.TypeChecking.Errors ()
import Agda.TypeChecking.Implicit (implicitArgs)
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import {-# SOURCE #-} Agda.TypeChecking.Constraints
import {-# SOURCE #-} Agda.TypeChecking.Rules.Term (checkArguments)
import {-# SOURCE #-} Agda.TypeChecking.MetaVars
import {-# SOURCE #-} Agda.TypeChecking.Conversion

import Agda.Utils.Except ( MonadError(catchError, throwError), runExceptT )
import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)

#include "undefined.h"
import Agda.Utils.Impossible

-- | A candidate solution for an instance meta is a term with its type.
type Candidate  = (Term, Type)
type Candidates = [Candidate]

-- | Compute a list of instance candidates.
--   'Nothing' if type is a meta, error if type is not eligible
--   for instance search.
initialIFSCandidates :: Type -> TCM (Maybe Candidates)
initialIFSCandidates t = do
  cands1 <- getContextVars
  otn <- getOutputTypeName t
  case otn of
    NoOutputTypeName -> typeError $ GenericError $ "Instance search can only be used to find elements in a named type"
    OutputTypeNameNotYetKnown -> return Nothing
    OutputTypeName n -> do
      cands2 <- getScopeDefs n
      return $ Just $ cands1 ++ cands2
  where
    -- get a list of variables with their type, relative to current context
    getContextVars :: TCM Candidates
    getContextVars = do
      ctx <- getContext
      let vars = [ (var i, raise (i + 1) t)
                 | (Dom info (x, t), i) <- zip ctx [0..]
                 , not (unusableRelevance $ argInfoRelevance info)
                 ]
      -- get let bindings
      env <- asks envLetBindings
      env <- mapM (getOpen . snd) $ Map.toList env
      let lets = [ (v,t)
                 | (v, Dom info t) <- env
                 , not (unusableRelevance $ argInfoRelevance info)
                 ]
      return $ vars ++ lets

    getScopeDefs :: QName -> TCM Candidates
    getScopeDefs n = do
      instanceDefs <- getInstanceDefs
      rel          <- asks envRelevance
      let qs = fromMaybe [] $ Map.lookup n instanceDefs
      catMaybes <$> mapM (candidate rel) qs

    candidate :: Relevance -> QName -> TCM (Maybe Candidate)
    candidate rel q =
      -- Andreas, 2012-07-07:
      -- we try to get the info for q
      -- while opening a module, q may be in scope but not in the signature
      -- in this case, we just ignore q (issue 674)
      flip catchError handle $ do
        def <- getConstInfo q
        let r = defRelevance def
        if not (r `moreRelevant` rel) then return Nothing else do
          t   <- defType <$> instantiateDef def
          args <- freeVarsToApply q
          let v = case theDef def of
               -- drop parameters if it's a projection function...
               Function{ funProjection = Just p } -> projDropPars p `apply` args
               -- Andreas, 2014-08-19: constructors cannot be declared as
               -- instances (at least as of now).
               -- I do not understand why the Constructor case is not impossible.
               -- Ulf, 2014-08-20: constructors are always instances.
               Constructor{ conSrcCon = c }       -> Con c []
               _                                  -> Def q $ map Apply args
          return $ Just (v, t)
      where
        -- unbound constant throws an internal error
        handle (TypeError _ (Closure {clValue = InternalError _})) = return Nothing
        handle err                                                 = throwError err

-- | @initializeIFSMeta s t@ generates an instance meta of type @t@
--   with suggested name @s@.
initializeIFSMeta :: String -> Type -> TCM Term
initializeIFSMeta s t = do
  t <- reduce t  -- see Issue 1321
  cands <- initialIFSCandidates t
  newIFSMeta s t cands

-- | @findInScope m (v,a)s@ tries to instantiate on of the types @a@s
--   of the candidate terms @v@s to the type @t@ of the metavariable @m@.
--   If successful, meta @m@ is solved with the instantiation of @v@.
--   If unsuccessful, the constraint is regenerated, with possibly reduced
--   candidate set.
--   The list of candidates is equal to @Nothing@ when the type of the meta
--   wasn't known when the constraint was generated. In that case, try to find
--   its type again.
findInScope :: MetaId -> Maybe Candidates -> TCM ()
findInScope m Nothing = do
  -- Andreas, 2015-02-07: New metas should be created with range of the
  -- current instance meta, thus, we set the range.
  mv <- lookupMeta m
  setCurrentRange mv $ do
  reportSLn "tc.instance" 20 $ "The type of the FindInScope constraint isn't known, trying to find it again."
  t <- getMetaType m
  cands <- initialIFSCandidates t
  case cands of
    Nothing -> addConstraint $ FindInScope m Nothing
    Just {} -> findInScope m cands
findInScope m (Just cands) = whenJustM (findInScope' m cands) $ addConstraint . FindInScope m . Just

-- | Result says whether we need to add constraint, and if so, the set of
--   remaining candidates.
findInScope' :: MetaId -> Candidates -> TCM (Maybe Candidates)
findInScope' m cands = ifM (isFrozen m) (return (Just cands)) $ do
  -- Andreas, 2013-12-28 issue 1003:
  -- If instance meta is already solved, simply discard the constraint.
  ifM (isInstantiatedMeta m) (return Nothing) $ do
  -- Andreas, 2015-02-07: New metas should be created with range of the
  -- current instance meta, thus, we set the range.
  mv <- lookupMeta m
  setCurrentRange mv $ do
  reportSLn "tc.instance" 15 $
    "findInScope 2: constraint: " ++ prettyShow m ++ "; candidates left: " ++ show (length cands)
  t <- normalise =<< getMetaTypeInContext m
  reportSDoc "tc.instance" 15 $ text "findInScope 3: t =" <+> prettyTCM t
  reportSLn "tc.instance" 70 $ "findInScope 3: t: " ++ show t
  -- If there are recursive instances, it's not safe to instantiate
  -- metavariables in the goal, so we freeze them before checking candidates.
  -- Metas that are rigidly constrained need not be frozen.
  isRec <- orM $ map (isRecursive . unEl . snd) cands
  let shouldFreeze rigid m
        | elem m rigid = return False
        | otherwise    = not <$> isFrozen m
  metas <- if not isRec then return [] else do
    rigid <- rigidlyConstrainedMetas
    filterM (shouldFreeze rigid) (allMetas t)
  forM_ metas $ \ m -> updateMetaVar m $ \ mv -> mv { mvFrozen = Frozen }
  cands <- checkCandidates m t cands
  reportSLn "tc.instance" 15 $
    "findInScope 4: cands left: " ++ show (length cands)
  unfreezeMeta metas
  case cands of

    [] -> do
      reportSDoc "tc.instance" 15 $
        text "findInScope 5: not a single candidate found..."
      typeError $ IFSNoCandidateInScope t

    [(term, t')] -> do
      reportSDoc "tc.instance" 15 $ vcat
        [ text "findInScope 5: found one candidate"
        , nest 2 $ prettyTCM term
        , text "of type " <+> prettyTCM t'
        , text "for type" <+> prettyTCM t
        ]

      -- If t' takes initial hidden and instance arguments, apply them.
      -- Taking also instance arguments facilitates recursive instance search.
      (args, t'') <- implicitArgs (-1) notVisible t'
      leqType t'' t
      ctxArgs <- getContextArgs
      v <- (`applyDroppingParameters` args) =<< reduce term
      assignV DirEq m ctxArgs v
      reportSDoc "tc.instance" 10 $ vcat
        [ text "solved by instance search:"
        , prettyTCM m <+> text ":=" <+> prettyTCM v
        ]
      return Nothing

    cs -> do
      reportSDoc "tc.instance" 15 $
        text ("findInScope 5: more than one candidate found: ") <+>
        prettyTCM (List.map fst cs)
      return (Just cs)
  where
    -- | Check whether a type is a function type with an instance domain.
    isRecursive :: Term -> TCM Bool
    isRecursive v = do
      v <- reduce v
      case ignoreSharing v of
        Pi (Dom info _) t ->
          if getHiding info == Instance then return True else
            isRecursive $ unEl $ unAbs t
        _ -> return False

-- | A meta _M is rigidly constrained if there is a constraint _M us == D vs,
-- for inert D. Such metas can safely be instantiated by recursive instance
-- search, since the constraint limits the solution space.
rigidlyConstrainedMetas :: TCM [MetaId]
rigidlyConstrainedMetas = do
  cs <- (++) <$> use stSleepingConstraints <*> use stAwakeConstraints
  catMaybes <$> mapM rigidMetas cs
  where
    isRigid v =
      case v of
        Def f _ -> return True
          -- def <- getConstInfo f
          -- case theDef def of
          --   Record{}   -> return True
          --   Datatype{} -> return True
          --   Axiom{}    -> return True
          --   _
        Con{} -> return True
        Lit{} -> return True
        Var{} -> return True
        _ -> return False
    rigidMetas c =
      case clValue $ theConstraint c of
        ValueCmp _ _ u v ->
          case (u, v) of
            (MetaV m _, _) -> ifM (isRigid v) (return $ Just m) (return Nothing)
            (_, MetaV m _) -> ifM (isRigid u) (return $ Just m) (return Nothing)
            _              -> return Nothing
        ElimCmp{}     -> return Nothing
        TypeCmp{}     -> return Nothing
        TelCmp{}      -> return Nothing
        SortCmp{}     -> return Nothing
        LevelCmp{}    -> return Nothing
        UnBlock{}     -> return Nothing
        Guarded{}     -> return Nothing  -- don't look inside Guarded, since the inner constraint might not fire
        IsEmpty{}     -> return Nothing
        FindInScope{} -> return Nothing

-- | Given a meta @m@ of type @t@ and a list of candidates @cands@,
-- @checkCandidates m t cands@ returns a refined list of valid candidates.
checkCandidates :: MetaId -> Type -> Candidates -> TCM Candidates
checkCandidates m t cands = localTCState $ disableDestructiveUpdate $ do
  -- for candidate checking, we don't take into account other IFS
  -- constraints
  dropConstraints (isIFSConstraint . clValue . theConstraint)
  cands <- filterM (uncurry $ checkCandidateForMeta m t) cands
  -- Drop all candidates which are equal to the first one
  dropSameCandidates cands
  where
    checkCandidateForMeta :: MetaId -> Type -> Term -> Type -> TCM Bool
    checkCandidateForMeta m t term t' = do
      -- Andreas, 2015-02-07: New metas should be created with range of the
      -- current instance meta, thus, we set the range.
      mv <- lookupMeta m
      setCurrentRange mv $ do
      verboseBracket "tc.instance" 20 ("checkCandidateForMeta " ++ prettyShow m) $ do
      liftTCM $ flip catchError handle $ do
        reportSLn "tc.instance" 70 $ "  t: " ++ show t ++ "\n  t':" ++ show t' ++ "\n  term: " ++ show term ++ "."
        reportSDoc "tc.instance" 20 $ vcat
          [ text "checkCandidateForMeta"
          , text "t    =" <+> prettyTCM t
          , text "t'   =" <+> prettyTCM t'
          , text "term =" <+> prettyTCM term
          ]
        -- domi: we assume that nothing below performs direct IO
        -- (except for logging and such, I guess)
        localTCState $ do

          -- Apply hidden and instance arguments (recursive inst. search!).
          (args, t'') <- implicitArgs (-1) notVisible t'

          reportSDoc "tc.instance" 20 $
            text "instance search: checking" <+> prettyTCM t''
            <+> text "<=" <+> prettyTCM t
          -- if constraints remain, we abort, but keep the candidate
          flip (ifNoConstraints_ $ leqType t'' t) (const $ return True) $ do

          ctxArgs <- getContextArgs
          v <- (`applyDroppingParameters` args) =<< reduce term
          reportSDoc "tc.instance" 15 $ vcat
            [ text "instance search: attempting"
            , nest 2 $ prettyTCM m <+> text ":=" <+> prettyTCM v
            ]
          assign DirEq m ctxArgs v
--          assign m ctxArgs (term `apply` args)
          -- make a pass over constraints, to detect cases where some are made
          -- unsolvable by the assignment, but don't do this for FindInScope's
          -- to prevent loops. We currently also ignore UnBlock constraints
          -- to be on the safe side.
          solveAwakeConstraints' True
          return True
      where
        handle :: TCErr -> TCM Bool
        handle err = do
          reportSDoc "tc.instance" 50 $
            text "assignment failed:" <+> prettyTCM err
          return False

    isIFSConstraint :: Constraint -> Bool
    isIFSConstraint FindInScope{} = True
    isIFSConstraint UnBlock{}     = True -- otherwise test/fail/Issue723 loops
    isIFSConstraint _             = False

    -- Drop all candidates which are judgmentally equal to the first one.
    -- This is sufficient to reduce the list to a singleton should all be equal.
    dropSameCandidates :: Candidates -> TCM Candidates
    dropSameCandidates cands = do
      case cands of
        []            -> return cands
        c@(v,a) : vas -> (c:) <$> dropWhileM equal vas
          where
            equal (v',a') = dontAssignMetas $ ifNoConstraints_ (equalType a a' >> equalTerm a v v')
                              {- then -} (return True)
                              {- else -} (\ _ -> return False)
                            `catchError` (\ _ -> return False)

-- | To preserve the invariant that a constructor is not applied to its
--   parameter arguments, we explicitly check whether function term
--   we are applying to arguments is a unapplied constructor.
--   In this case we drop the first 'conPars' arguments.
--   See Issue670a.
--   Andreas, 2013-11-07 Also do this for projections, see Issue670b.
applyDroppingParameters :: Term -> Args -> TCM Term
applyDroppingParameters t vs = do
  let fallback = return $ t `apply` vs
  case ignoreSharing t of
    Con c [] -> do
      def <- theDef <$> getConInfo c
      case def of
        Constructor {conPars = n} -> return $ Con c (genericDrop n vs)
        _ -> __IMPOSSIBLE__
    Def f [] -> do
      mp <- isProjection f
      case mp of
        Just Projection{projIndex = n} -> do
          case drop n vs of
            []     -> return t
            u : us -> (`apply` us) <$> applyDef f u
        _ -> fallback
    _ -> fallback
