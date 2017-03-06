{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.InstanceArguments where

import Control.Applicative hiding (empty)
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List as List

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Scope.Base (isNameInScope)

import Agda.TypeChecking.Errors ()
import Agda.TypeChecking.Implicit (implicitArgs)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Records
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
import Agda.Utils.Functor
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Null (empty)

#include "undefined.h"
import Agda.Utils.Impossible

-- | Compute a list of instance candidates.
--   'Nothing' if type is a meta, error if type is not eligible
--   for instance search.
initialIFSCandidates :: Type -> TCM (Maybe [Candidate])
initialIFSCandidates t = do
  otn <- getOutputTypeName t
  case otn of
    NoOutputTypeName -> typeError $ GenericError $
      "Instance search can only be used to find elements in a named type"
    OutputTypeNameNotYetKnown -> return Nothing
    OutputTypeVar    -> Just <$> getContextVars
    OutputTypeName n -> Just <$> do (++) <$> getContextVars <*> getScopeDefs n
  where
    -- get a list of variables with their type, relative to current context
    getContextVars :: TCM [Candidate]
    getContextVars = do
      ctx <- getContext
          -- Context variables with their types lifted to live in the full context
      let varsAndRaisedTypes = [ (var i, raise (i + 1) t) | (i, t) <- zip [0..] ctx ]
          vars = [ Candidate x t ExplicitStayExplicit (argInfoOverlappable info)
                 | (x, Dom{domInfo = info, unDom = (_, t)}) <- varsAndRaisedTypes
                 , getHiding info == Instance
                 , not (unusableRelevance $ argInfoRelevance info)
                 ]

      -- {{}}-fields of variables are also candidates
      let cxtAndTypes = [ (x, t) | (x, Dom{unDom = (_, t)}) <- varsAndRaisedTypes ]
      fields <- concat <$> mapM instanceFields (reverse cxtAndTypes)
      reportSDoc "tc.instance.fields" 30 $
        if null fields then text "no instance field candidates" else
          text "instance field candidates" $$ do
            nest 2 $ vcat
              [ sep [ (if overlap then text "overlap" else empty) <+> prettyTCM v <+> text ":"
                    , nest 2 $ prettyTCM t
                    ]
              | Candidate v t _ overlap <- fields
              ]

      -- get let bindings
      env <- asks envLetBindings
      env <- mapM (getOpen . snd) $ Map.toList env
      let lets = [ Candidate v t ExplicitStayExplicit False
                 | (v, Dom{domInfo = info, unDom = t}) <- env
                 , getHiding info == Instance
                 , not (unusableRelevance $ argInfoRelevance info)
                 ]
      return $ vars ++ fields ++ lets

    etaExpand etaOnce t =
      isEtaRecordType t >>= \case
        Nothing | etaOnce -> do
          isRecordType t >>= \case
            Nothing         -> return Nothing
            Just (r, vs, _) -> do
              m <- currentModule
              -- Are we inside the record module? If so it's safe and desirable
              -- to eta-expand once (issue #2320).
              if qnameToList r `isPrefixOf` mnameToList m
                then return (Just (r, vs))
                else return Nothing
        r -> return r

    instanceFields = instanceFields' True
    instanceFields' etaOnce (v, t) =
      caseMaybeM (etaExpand etaOnce =<< reduce t) (return []) $ \ (r, pars) -> do
        (tel, args) <- forceEtaExpandRecord r pars v
        let types = map unDom $ applySubst (parallelS $ reverse $ map unArg args) (flattenTel tel)
        fmap concat $ forM (zip args types) $ \ (arg, t) ->
          ([ Candidate (unArg arg) t ExplicitStayExplicit (argInfoOverlappable $ argInfo arg)
           | getHiding arg == Instance ] ++) <$>
          instanceFields' False (unArg arg, t)

    getScopeDefs :: QName -> TCM [Candidate]
    getScopeDefs n = do
      instanceDefs <- getInstanceDefs
      rel          <- asks envRelevance
      let qs = maybe [] Set.toList $ Map.lookup n instanceDefs
      catMaybes <$> mapM (candidate rel) qs

    candidate :: Relevance -> QName -> TCM (Maybe Candidate)
    candidate rel q = ifNotM (isNameInScope q <$> getScope) (return Nothing) $ do
      -- Andreas, 2012-07-07:
      -- we try to get the info for q
      -- while opening a module, q may be in scope but not in the signature
      -- in this case, we just ignore q (issue 674)
      flip catchError handle $ do
        def <- getConstInfo q
        if not (defRelevance def `moreRelevant` rel) then return Nothing else do
          -- Andreas, 2017-01-14: instantiateDef is a bit of an overkill
          -- if we anyway get the freeVarsToApply
          -- WAS: t <- defType <$> instantiateDef def
          args <- freeVarsToApply q
          let t = defType def `piApply` args
          let v = case theDef def of
               -- drop parameters if it's a projection function...
               Function{ funProjection = Just p } -> projDropParsApply p ProjSystem args
               -- Andreas, 2014-08-19: constructors cannot be declared as
               -- instances (at least as of now).
               -- I do not understand why the Constructor case is not impossible.
               -- Ulf, 2014-08-20: constructors are always instances.
               Constructor{ conSrcCon = c }       -> Con c ConOSystem []
               _                                  -> Def q $ map Apply args
          return $ Just $ Candidate v t ExplicitToInstance False
      where
        -- unbound constant throws an internal error
        handle (TypeError _ (Closure {clValue = InternalError _})) = return Nothing
        handle err                                                 = throwError err

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
    reportSLn "tc.instance" 70 $ "findInScope 1: t: " ++ show t

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
  -- Ulf, 2016-12-06 issue 2325: But only if *fully* instantiated.
  ifM (isFullyInstantiatedMeta m) (return Nothing) $ do
    -- Andreas, 2015-02-07: New metas should be created with range of the
    -- current instance meta, thus, we set the range.
    mv <- lookupMeta m
    setCurrentRange mv $ do
      reportSLn "tc.instance" 15 $
        "findInScope 2: constraint: " ++ prettyShow m ++ "; candidates left: " ++ show (length cands)
      reportSDoc "tc.instance" 60 $ nest 2 $ vcat
        [ sep [ (if overlap then text "overlap" else empty) <+> prettyTCM v <+> text ":"
              , nest 2 $ prettyTCM t ] | Candidate v t _ overlap <- cands ]
      reportSDoc "tc.instance" 70 $ text "raw" $$ do
       nest 2 $ vcat
        [ sep [ (if overlap then text "overlap" else empty) <+> (text . show) v <+> text ":"
              , nest 2 $ (text . show) t ] | Candidate v t _ overlap <- cands ]
      t <- normalise =<< getMetaTypeInContext m
      reportSLn "tc.instance" 70 $ "findInScope 2: t: " ++ show t
      insidePi t $ \ t -> do
      reportSDoc "tc.instance" 15 $ text "findInScope 3: t =" <+> prettyTCM t
      reportSLn "tc.instance" 70 $ "findInScope 3: t: " ++ show t

      -- If one of the arguments of the typeclass is a meta which is not rigidly
      -- constrained, then don’t do anything because it may loop.
      let abortNonRigid m = do
            reportSLn "tc.instance" 15 $
              "aborting due to non-rigidly constrained meta " ++ show m
            return $ Just (cands, Just m)
      ifJustM (areThereNonRigidMetaArguments (unEl t)) abortNonRigid $ {-else-} do

        mcands <- checkCandidates m t cands
        debugConstraints
        case mcands of

          Just [] -> do
            reportSDoc "tc.instance" 15 $
              text "findInScope 5: not a single candidate found..."
            typeError $ IFSNoCandidateInScope t

          Just [Candidate term t' _ _] -> do
            reportSDoc "tc.instance" 15 $ vcat
              [ text "findInScope 5: solved by instance search using the only candidate"
              , nest 2 $ prettyTCM term
              , text "of type " <+> prettyTCM t'
              , text "for type" <+> prettyTCM t
              ]

            -- If we actually solved the constraints we should wake up any held
            -- instance constraints, to make sure we don't forget about them.
            wakeConstraints (return . const True)
            solveAwakeConstraints' False
            return Nothing  -- We’re done

          _ -> do
            let cs = fromMaybe cands mcands -- keep the current candidates if Nothing
            reportSDoc "tc.instance" 15 $
              text ("findInScope 5: refined candidates: ") <+>
              prettyTCM (List.map candidateTerm cs)
            return (Just (cs, Nothing))

-- | Precondition: type is spine reduced and ends in a Def or a Var.
insidePi :: Type -> (Type -> TCM a) -> TCM a
insidePi t ret =
  case ignoreSharing $ unEl t of
    Pi a b     -> addContext' (absName b, a) $ insidePi (unAbs b) ret
    Def{}      -> ret t
    Var{}      -> ret t
    Sort{}     -> __IMPOSSIBLE__
    Con{}      -> __IMPOSSIBLE__
    Lam{}      -> __IMPOSSIBLE__
    Lit{}      -> __IMPOSSIBLE__
    Level{}    -> __IMPOSSIBLE__
    MetaV{}    -> __IMPOSSIBLE__
    Shared{}   -> __IMPOSSIBLE__
    DontCare{} -> __IMPOSSIBLE__

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
        ValueCmpOnFace{} -> return Nothing -- applying the face could remove the meta
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
isRigid i = do
  rigid <- rigidlyConstrainedMetas
  return (elem i rigid)

-- | Returns True if one of the arguments of @t@ is a meta which isn’t rigidly
--   constrained. Note that level metas are never considered rigidly constrained
--   (#1865).
areThereNonRigidMetaArguments :: Term -> TCM (Maybe MetaId)
areThereNonRigidMetaArguments t = case ignoreSharing t of
    Def n args -> do
      TelV tel _ <- telView . defType =<< getConstInfo n
      let varOccs EmptyTel           = []
          varOccs (ExtendTel a btel)
            | getRelevance a == Irrelevant = WeaklyRigid : varOccs tel  -- #2171: ignore irrelevant arguments
            | otherwise                    = occurrence 0 tel : varOccs tel
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
    areThereNonRigidMetaArgs (Proj{}  : xs) = areThereNonRigidMetaArgs xs
    areThereNonRigidMetaArgs (Apply x : xs) = do
      ifJustM (isNonRigidMeta $ unArg x) (return . Just) (areThereNonRigidMetaArgs xs)
    areThereNonRigidMetaArgs (IApply x y v : xs) = areThereNonRigidMetaArgs $ map (Apply . defaultArg) [x, y, v] ++ xs -- TODO Andrea HACK


    isNonRigidMeta :: Term -> TCM (Maybe MetaId)
    isNonRigidMeta v =
      case ignoreSharing v of
        Def _ es  -> areThereNonRigidMetaArgs es
        Var _ es  -> areThereNonRigidMetaArgs es
        Con _ _ vs-> areThereNonRigidMetaArgs (map Apply vs)
        MetaV i _ -> ifM (isRigid i) (return Nothing) $ do
          -- Ignore unconstrained level and size metas (#1865)
          mlvl <- getBuiltinDefName builtinLevel
          (msz, mszlt) <- getBuiltinSize
          let ok = catMaybes [ mlvl, msz ]  -- , mszlt ]  -- ?! Andreas, 2016-12-22
            -- @Ulf: are SIZELT metas excluded on purpose?
            -- How to you know the level/size meta is unconstrained?
          o <- getOutputTypeName . jMetaType . mvJudgement =<< lookupMeta i
          case o of
            OutputTypeName l | elem l ok -> return Nothing
            _ -> return $ Just i
        Lam _ t   -> isNonRigidMeta (unAbs t)
        _         -> return Nothing

-- | Apply the computation to every argument in turn by reseting the state every
--   time. Return the list of the arguments giving the result True.
--
--   If the resulting list contains exactly one element, then the state is the
--   same as the one obtained after running the corresponding computation. In
--   all the other cases, the state is reseted.
filterResetingState :: MetaId -> [Candidate] -> (Candidate -> TCM YesNoMaybe) -> TCM [Candidate]
filterResetingState m cands f = disableDestructiveUpdate $ do
  ctxArgs  <- getContextArgs
  let ctxElims = map Apply ctxArgs
      tryC c = do
        ok <- f c
        v  <- instantiateFull (MetaV m ctxElims)
        a  <- instantiateFull =<< (`piApplyM` ctxArgs) =<< getMetaType m
        return (ok, v, a)
  result <- mapM (\c -> do bs <- localTCStateSaving (tryC c); return (c, bs)) cands

  -- Check that there aren't any hard failures
  case [ err | (_, ((HellNo err, _, _), _)) <- result ] of
    err : _ -> throwError err
    []      -> return ()

  let result' = [ (c, v, a, s) | (c, ((r, v, a), s)) <- result, not (isNo r) ]
      noMaybes = null [ Maybe | (_, ((Maybe, _, _), _)) <- result ]
            -- It's not safe to compare maybes for equality because they might
            -- not have instantiated at all.
  result <- if noMaybes then dropSameCandidates m result' else return result'
  case result of
    [(c, _, _, s)] -> [c] <$ put s
    _              -> return [ c | (c, _, _, _) <- result ]

-- Drop all candidates which are judgmentally equal to the first one.
-- This is sufficient to reduce the list to a singleton should all be equal.
dropSameCandidates :: MetaId -> [(Candidate, Term, Type, a)] -> TCM [(Candidate, Term, Type, a)]
dropSameCandidates m cands0 = do
  metas <- Set.fromList . Map.keys <$> getMetaStore
  let freshMetas x = not $ Set.null $ Set.difference (Set.fromList $ allMetas x) metas

  -- Take overlappable candidates into account
  let cands =
        case partition (\ (c, _, _, _) -> candidateOverlappable c) cands0 of
          (cand : _, []) -> [cand]  -- only overlappable candidates: pick the first one
          _              -> cands0  -- otherwise require equality

  reportSDoc "tc.instance" 50 $ vcat
    [ text "valid candidates:"
    , nest 2 $ vcat [ if freshMetas (v, a) then text "(redacted)" else
                      sep [ prettyTCM v <+> text ":", nest 2 $ prettyTCM a ]
                    | (_, v, a, _) <- cands ] ]
  rel <- getMetaRelevance <$> lookupMeta m
  case cands of
    []            -> return cands
    cvd@(_, v, a, _) : vas -> do
        if freshMetas (v, a)
          then return (cvd : vas)
          else (cvd :) <$> dropWhileM equal vas
      where
        equal _ | isIrrelevant rel = return True
        equal (_, v', a', _)
            | freshMetas (v', a') = return False  -- If there are fresh metas we can't compare
            | otherwise           =
          verboseBracket "tc.instance" 30 "checkEqualCandidates" $ do
          reportSDoc "tc.instance" 30 $ sep [ prettyTCM v <+> text "==", nest 2 $ prettyTCM v' ]
          localTCState $ dontAssignMetas $ ifNoConstraints_ (equalType a a' >> equalTerm a v v')
                             {- then -} (return True)
                             {- else -} (\ _ -> return False)
                             `catchError` (\ _ -> return False)

data YesNoMaybe = Yes | No | Maybe | HellNo TCErr
  deriving (Show)

isNo :: YesNoMaybe -> Bool
isNo No = True
isNo _  = False

-- | Given a meta @m@ of type @t@ and a list of candidates @cands@,
-- @checkCandidates m t cands@ returns a refined list of valid candidates.
checkCandidates :: MetaId -> Type -> [Candidate] -> TCM (Maybe [Candidate])
checkCandidates m t cands = disableDestructiveUpdate $
  verboseBracket "tc.instance.candidates" 20 ("checkCandidates " ++ prettyShow m) $
  ifM (anyMetaTypes cands) (return Nothing) $
  holdConstraints (\ _ -> isIFSConstraint . clValue . theConstraint) $ Just <$> do
    reportSDoc "tc.instance.candidates" 20 $ nest 2 $ text "target:" <+> prettyTCM t
    reportSDoc "tc.instance.candidates" 20 $ nest 2 $ vcat
      [ text "candidates"
      , vcat [ text "-" <+> (if overlap then text "overlap" else empty) <+> prettyTCM v <+> text ":" <+> prettyTCM t
             | Candidate v t _ overlap <- cands ] ]
    cands' <- filterResetingState m cands (checkCandidateForMeta m t)
    reportSDoc "tc.instance.candidates" 20 $ nest 2 $ vcat
      [ text "valid candidates"
      , vcat [ text "-" <+> (if overlap then text "overlap" else empty) <+> prettyTCM v <+> text ":" <+> prettyTCM t
             | Candidate v t _ overlap <- cands' ] ]
    return cands'
  where
    anyMetaTypes :: [Candidate] -> TCM Bool
    anyMetaTypes [] = return False
    anyMetaTypes (Candidate _ a _ _ : cands) = do
      a <- instantiate a
      case ignoreSharing $ unEl a of
        MetaV{} -> return True
        _       -> anyMetaTypes cands

    checkDepth :: Term -> Type -> TCM YesNoMaybe -> TCM YesNoMaybe
    checkDepth c a k = locally eInstanceDepth succ $ do
      d        <- view eInstanceDepth
      maxDepth <- maxInstanceSearchDepth
      when (d > maxDepth) $ typeError $ InstanceSearchDepthExhausted c a maxDepth
      k

    checkCandidateForMeta :: MetaId -> Type -> Candidate -> TCM YesNoMaybe
    checkCandidateForMeta m t (Candidate term t' eti _) = checkDepth term t' $ do
      -- Andreas, 2015-02-07: New metas should be created with range of the
      -- current instance meta, thus, we set the range.
      mv <- lookupMeta m
      setCurrentRange mv $ do
        debugConstraints
        verboseBracket "tc.instance" 20 ("checkCandidateForMeta " ++ prettyShow m) $
          liftTCM $ runCandidateCheck $ do
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
            reportSDoc "tc.instance" 70 $ vcat
              [ text "instance search: checking (raw)"
              , nest 4 $ (text . show) t''
              , nest 2 $ text "<="
              , nest 4 $ (text . show) t
              ]
            v <- (`applyDroppingParameters` args) =<< reduce term
            reportSDoc "tc.instance" 15 $ vcat
              [ text "instance search: attempting"
              , nest 2 $ prettyTCM m <+> text ":=" <+> prettyTCM v
              ]
            reportSDoc "tc.instance" 70 $ nest 2 $
              text "candidate v = " <+> (text . show) v
            -- if constraints remain, we abort, but keep the candidate
            -- Jesper, 05-12-2014: When we abort, we should add a constraint to
            -- instantiate the meta at a later time (see issue 1377).
            ctxElims <- map Apply <$> getContextArgs
            guardConstraint (ValueCmp CmpEq t'' (MetaV m ctxElims) v) $ leqType t'' t
            -- make a pass over constraints, to detect cases where some are made
            -- unsolvable by the assignment, but don't do this for FindInScope's
            -- to prevent loops. We currently also ignore UnBlock constraints
            -- to be on the safe side.
            debugConstraints
            solveAwakeConstraints' True

            verboseS "tc.instance" 15 $ do
              sol <- instantiateFull (MetaV m ctxElims)
              case sol of
                MetaV m' _ | m == m' ->
                  reportSDoc "tc.instance" 15 $
                    sep [ text "instance search: maybe solution for" <+> prettyTCM m <> text ":"
                        , nest 2 $ prettyTCM v ]
                _ ->
                  reportSDoc "tc.instance" 15 $
                    sep [ text "instance search: found solution for" <+> prettyTCM m <> text ":"
                        , nest 2 $ prettyTCM sol ]
        where
          runCandidateCheck check =
            flip catchError handle $
            ifNoConstraints_ check
              (return Yes)
              (\ _ -> Maybe <$ reportSLn "tc.instance" 50 "assignment inconclusive")

          hardFailure :: TCErr -> Bool
          hardFailure (TypeError _ err) =
            case clValue err of
              InstanceSearchDepthExhausted{} -> True
              _                              -> False
          hardFailure _ = False

          handle :: TCErr -> TCM YesNoMaybe
          handle err
            | hardFailure err = return $ HellNo err
            | otherwise       = do
              reportSDoc "tc.instance" 50 $
                text "assignment failed:" <+> prettyTCM err
              return No

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
    Con c ci [] -> do
      def <- theDef <$> getConInfo c
      case def of
        Constructor {conPars = n} -> return $ Con c ci (genericDrop n vs)
        _ -> __IMPOSSIBLE__
    Def f [] -> do
      mp <- isProjection f
      case mp of
        Just Projection{projIndex = n} -> do
          case drop n vs of
            []     -> return t
            u : us -> (`apply` us) <$> applyDef ProjPrefix f u
        _ -> fallback
    _ -> fallback
