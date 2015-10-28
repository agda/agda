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
import Agda.Syntax.Internal as I

import Agda.TypeChecking.Errors ()
import Agda.TypeChecking.Implicit (implicitArgs)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Free

import {-# SOURCE #-} Agda.TypeChecking.Constraints
import {-# SOURCE #-} Agda.TypeChecking.MetaVars
import {-# SOURCE #-} Agda.TypeChecking.Conversion

import Agda.Utils.Except ( MonadError(catchError, throwError) )
import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)

#include "undefined.h"
import Agda.Utils.Impossible

-- | Compute a list of instance candidates.
--   'Nothing' if type is a meta, error if type is not eligible
--   for instance search.
initialIFSCandidates :: Type -> TCM (Maybe [Candidate])
initialIFSCandidates t = do
  cands1 <- getContextVars
  otn <- getOutputTypeName t
  case otn of
    NoOutputTypeName -> typeError $ GenericError $ "Instance search can only be used to find elements in a named type"
    OutputTypeNameNotYetKnown -> return Nothing
    OutputTypeVar -> return $ Just cands1
    OutputTypeName n -> do
      cands2 <- getScopeDefs n
      return $ Just $ cands1 ++ cands2
  where
    -- get a list of variables with their type, relative to current context
    getContextVars :: TCM [Candidate]
    getContextVars = do
      ctx <- getContext
      let vars = [ Candidate (var i) (raise (i + 1) t) ExplicitStayExplicit
                 | (Dom info (x, t), i) <- zip ctx [0..]
                 , not (unusableRelevance $ argInfoRelevance info)
                 ]
      -- get let bindings
      env <- asks envLetBindings
      env <- mapM (getOpen . snd) $ Map.toList env
      let lets = [ Candidate v t ExplicitStayExplicit
                 | (v, Dom info t) <- env
                 , not (unusableRelevance $ argInfoRelevance info)
                 ]
      return $ vars ++ lets

    getScopeDefs :: QName -> TCM [Candidate]
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
          return $ Just $ Candidate v t ExplicitToInstance
      where
        -- unbound constant throws an internal error
        handle (TypeError _ (Closure {clValue = InternalError _})) = return Nothing
        handle err                                                 = throwError err

-- | @initializeIFSMeta s t@ generates an instance meta of type @t@
--   with suggested name @s@, possibly with leading lambdas.
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
findInScope :: MetaId -> Maybe [Candidate] -> TCM ()
findInScope m Nothing = do
  -- Andreas, 2015-02-07: New metas should be created with range of the
  -- current instance meta, thus, we set the range.
  mv <- lookupMeta m
  setCurrentRange mv $ do
    reportSLn "tc.instance" 20 $ "The type of the FindInScope constraint isn't known, trying to find it again."
    t <- getMetaType m

--     -- We create a new meta (which can have additional leading lambdas, if the
--     -- type @t@ now happens to be a function type) and the associated constraint
--     newM <- initializeIFSMeta (miNameSuggestion $ mvInfo mv) t

--     -- ... and we assign it to the previous one
--     ctxElims <- map Apply <$> getContextArgs
--     solveConstraint $ ValueCmp CmpEq t (MetaV m ctxElims) newM

-- {-
    cands <- initialIFSCandidates t
    case cands of
      Nothing -> addConstraint $ FindInScope m Nothing Nothing
      Just {} -> findInScope m cands
-- -}
findInScope m (Just cands) =
  whenJustM (findInScope' m cands) $ (\ (cands, b) -> addConstraint $ FindInScope m b $ Just cands)

-- | Result says whether we need to add constraint, and if so, the set of
--   remaining candidates and an eventual blocking metavariable.
findInScope' :: MetaId -> [Candidate] -> TCM (Maybe ([Candidate], Maybe MetaId))
findInScope' m cands = ifM (isFrozen m) (return (Just (cands, Nothing))) $ do
  -- Andreas, 2013-12-28 issue 1003:
  -- If instance meta is already solved, simply discard the constraint.
  ifM (isInstantiatedMeta m) (return Nothing) $ do
    -- Andreas, 2015-02-07: New metas should be created with range of the
    -- current instance meta, thus, we set the range.
    mv <- lookupMeta m
    setCurrentRange mv $ do
      reportSLn "tc.instance" 15 $
        "findInScope 2: constraint: " ++ prettyShow m ++ "; candidates left: " ++ show (length cands)
      reportSDoc "tc.instance" 70 $ nest 2 $ vcat
        [ sep [ prettyTCM v <+> text ":", nest 2 $ prettyTCM t ] | Candidate v t _ <- cands ]
      t <- normalise =<< getMetaTypeInContext m
      reportSDoc "tc.instance" 15 $ text "findInScope 3: t =" <+> prettyTCM t
      reportSLn "tc.instance" 70 $ "findInScope 3: t: " ++ show t

      -- If one of the arguments of the typeclass is a meta which is not rigidly
      -- constrained, then don’t do anything because it may loop.
      ifJustM (areThereNonRigidMetaArguments (unEl t)) (\ m -> return (Just (cands, Just m))) $ do

        cands <- checkCandidates m t cands
        reportSLn "tc.instance" 15 $
          "findInScope 4: cands left: " ++ show (length cands)
        case cands of

          [] -> do
            reportSDoc "tc.instance" 15 $
              text "findInScope 5: not a single candidate found..."
            typeError $ IFSNoCandidateInScope t

          [Candidate term t' _] -> do
            reportSDoc "tc.instance" 15 $ vcat
              [ text "findInScope 5: solved by instance search using the only candidate"
              , nest 2 $ prettyTCM term
              , text "of type " <+> prettyTCM t'
              , text "for type" <+> prettyTCM t
              ]

            return Nothing  -- We’re done

          cs -> do
            reportSDoc "tc.instance" 15 $
              text ("findInScope 5: more than one candidate found: ") <+>
              prettyTCM (List.map candidateTerm cs)
            return (Just (cs, Nothing))
      where
        -- | Check whether a type is a function type with an instance or explicit domain.
        isRecursive :: Term -> TCM Bool
        isRecursive v = do
          v <- reduce v
          case ignoreSharing v of
            Pi (Dom info _) t ->
              if getHiding info /= Hidden then return True else
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
    isRigid v = do
      bv <- reduceB v
      case ignoreSharing <$> bv of
        Blocked{}    -> return False
        NotBlocked _ v -> case v of
          MetaV{}    -> return False
          Def f _    -> return True
          Con{}      -> return True
          Lit{}      -> return True
          Var{}      -> return True
          Sort{}     -> return True
          Pi{}       -> return True
          Level{}    -> return False
          DontCare{} -> return False
          Lam{}      -> __IMPOSSIBLE__
          Shared{}   -> __IMPOSSIBLE__
    rigidMetas c =
      case clValue $ theConstraint c of
        ValueCmp _ _ u v ->
          case (ignoreSharing u, ignoreSharing v) of
            (MetaV m us, _) | isJust (allApplyElims us) -> ifM (isRigid v) (return $ Just m) (return Nothing)
            (_, MetaV m vs) | isJust (allApplyElims vs) -> ifM (isRigid u) (return $ Just m) (return Nothing)
            _              -> return Nothing
        ElimCmp{}     -> return Nothing
        TypeCmp{}     -> return Nothing
        TelCmp{}      -> return Nothing
        SortCmp{}     -> return Nothing
        LevelCmp{}    -> return Nothing
        UnBlock{}     -> return Nothing
        Guarded{}     -> return Nothing  -- don't look inside Guarded, since the inner constraint might not fire
        IsEmpty{}     -> return Nothing
        CheckSizeLtSat{} -> return Nothing
        FindInScope{} -> return Nothing

isRigid :: MetaId -> TCM Bool
isRigid id = do
  rigid <- rigidlyConstrainedMetas
  return (elem id rigid)

-- | Returns True if one of the arguments of @t@ is a meta which isn’t rigidly constrained
areThereNonRigidMetaArguments :: Term -> TCM (Maybe MetaId)
areThereNonRigidMetaArguments t = case ignoreSharing t of
    Def n args -> do
      TelV tel _ <- telView . defType =<< getConstInfo n
      let varOccs EmptyTel           = []
          varOccs (ExtendTel _ btel) = occurrence 0 tel : varOccs tel
            where tel = unAbs btel
          rigid StronglyRigid = True
          rigid Unguarded     = True
          rigid WeaklyRigid   = True
          rigid _             = False
      reportSDoc "tc.instance.rigid" 70 $ text "class args:" <+> prettyTCM tel $$
                                          nest 2 (text $ "used: " ++ show (varOccs tel))
      areThereNonRigidMetaArgs [ arg | (o, arg) <- zip (varOccs tel) args, not $ rigid o ]
    Var n args -> return Nothing  -- TODO check what’s the right thing to do, doing the same
                                  -- thing as above makes some examples fail
    Sort{}   -> __IMPOSSIBLE__
    Con{}    -> __IMPOSSIBLE__
    Lam{}    -> __IMPOSSIBLE__
    Lit{}    -> __IMPOSSIBLE__
    Level{}  -> __IMPOSSIBLE__
    MetaV{}  -> __IMPOSSIBLE__
    Pi{}     -> __IMPOSSIBLE__
    Shared{} -> __IMPOSSIBLE__
    DontCare{} -> __IMPOSSIBLE__
  where
    areThereNonRigidMetaArgs :: Elims -> TCM (Maybe MetaId)
    areThereNonRigidMetaArgs []             = return Nothing
    areThereNonRigidMetaArgs (Proj _ : _)   = __IMPOSSIBLE__
    areThereNonRigidMetaArgs (Apply x : xs) = do
      ifJustM (isNonRigidMeta $ unArg x) (return . Just) (areThereNonRigidMetaArgs xs)

    isNonRigidMeta :: Term -> TCM (Maybe MetaId)
    isNonRigidMeta v =
      case ignoreSharing v of
        MetaV i _ -> ifM (not <$> isRigid i) (return (Just i)) (return Nothing)
        Lam _ t   -> isNonRigidMeta (unAbs t)
        _         -> return Nothing

-- | Apply the computation to every argument in turn by reseting the state every
--   time. Return the list of the arguments giving the result True.
--
--   If the resulting list contains exactly one element, then the state is the
--   same as the one obtained after running the corresponding computation. In
--   all the other cases, the state is reseted.
filterResetingState :: MetaId -> [Candidate] -> (Candidate -> TCM Bool) -> TCM [Candidate]
filterResetingState m cands f = disableDestructiveUpdate $ do
  result <- mapM (\c -> do bs <- localTCStateSaving (f c); return (c, bs)) cands
  let result' = [ (c, s) | (c, (True, s)) <- result ]
  result <- dropSameCandidates m result'
  case result of
    [(c, s)] -> [c] <$ put s
    _        -> return $ map fst result

-- Drop all candidates which are judgmentally equal to the first one.
-- This is sufficient to reduce the list to a singleton should all be equal.
dropSameCandidates :: MetaId -> [(Candidate, a)] -> TCM [(Candidate, a)]
dropSameCandidates m cands = do
  reportSDoc "tc.instance" 50 $ text "valid candidates:" $$ nest 2 (vcat $ map (prettyTCM . candidateTerm . fst) cands)
  rel <- getMetaRelevance <$> lookupMeta m
  case cands of
    []            -> return cands
    (Candidate v a eti, d) : vas -> ((Candidate v a eti, d):) <$> dropWhileM equal vas
      where
        equal _ | isIrrelevant rel = return True
        equal (Candidate v' a' eti', _) =
          verboseBracket "tc.instance" 30 "checkEqualCandidates" $ do
          reportSDoc "tc.instance" 30 $ sep [ prettyTCM v <+> text "==", nest 2 $ prettyTCM v' ]
          localTCState $ dontAssignMetas $ ifNoConstraints_ (equalType a a' >> equalTerm a v v')
                             {- then -} (return True)
                             {- else -} (\ _ -> return False)
                             `catchError` (\ _ -> return False)

-- | Given a meta @m@ of type @t@ and a list of candidates @cands@,
-- @checkCandidates m t cands@ returns a refined list of valid candidates.
checkCandidates :: MetaId -> Type -> [Candidate] -> TCM [Candidate]
checkCandidates m t cands = disableDestructiveUpdate $ do
  verboseBracket "tc.instance.candidates" 20 ("checkCandidates " ++ prettyShow m) $ do
    reportSDoc "tc.instance.candidates" 20 $ nest 2 $ text "target:" <+> prettyTCM t
    reportSDoc "tc.instance.candidates" 20 $ nest 2 $ vcat
      [ text "candidates"
      , vcat [ text "-" <+> prettyTCM v <+> text ":" <+> prettyTCM t | Candidate v t _ <- cands ] ]
    cands' <- filterResetingState m cands (checkCandidateForMeta m t)
    reportSDoc "tc.instance.candidates" 20 $ nest 2 $ vcat
      [ text "valid candidates"
      , vcat [ text "-" <+> prettyTCM v <+> text ":" <+> prettyTCM t | Candidate v t _ <- cands' ] ]
    return cands'
  where
    checkCandidateForMeta :: MetaId -> Type -> Candidate -> TCM Bool
    checkCandidateForMeta m t (Candidate term t' eti) = do
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

            -- Apply hidden and instance arguments (recursive inst. search!).
            (args, t'') <- implicitArgs (-1) (\h -> h /= NotHidden || eti == ExplicitToInstance) t'

            reportSDoc "tc.instance" 20 $
              text "instance search: checking" <+> prettyTCM t''
              <+> text "<=" <+> prettyTCM t
            ctxElims <- map Apply <$> getContextArgs
            v <- (`applyDroppingParameters` args) =<< reduce term
            reportSDoc "tc.instance" 15 $ vcat
              [ text "instance search: attempting"
              , nest 2 $ prettyTCM m <+> text ":=" <+> prettyTCM v
              ]
            -- if constraints remain, we abort, but keep the candidate
            -- Jesper, 05-12-2014: When we abort, we should add a constraint to
            -- instantiate the meta at a later time (see issue 1377).
            guardConstraint (ValueCmp CmpEq t'' (MetaV m ctxElims) v) $ leqType t'' t
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
