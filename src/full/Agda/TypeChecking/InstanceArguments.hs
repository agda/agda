{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.InstanceArguments
  ( findInstance
  , isInstanceConstraint
  , shouldPostponeInstanceSearch
  , postponeInstanceConstraints
  ) where

import Control.Monad.Reader
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List
import Data.Function (on)
import Data.Monoid hiding ((<>))

import Agda.Interaction.Options (optOverlappingInstances, optQualifiedInstances)

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name (isQualified)
import Agda.Syntax.Position
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.MetaVars
import Agda.Syntax.Scope.Base (isNameInScope, inverseScopeLookup', AllowAmbiguousNames(..))

import Agda.TypeChecking.Errors () --instance only
import Agda.TypeChecking.Implicit (implicitArgs)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Records
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import {-# SOURCE #-} Agda.TypeChecking.Constraints
import {-# SOURCE #-} Agda.TypeChecking.Conversion

import qualified Agda.Benchmarking as Benchmark
import Agda.TypeChecking.Monad.Benchmark (billTo)

import Agda.Utils.Either
import Agda.Utils.Except
import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Null (empty)

import Agda.Utils.Impossible

-- | Compute a list of instance candidates.
--   'Nothing' if target type or any context type is a meta, error if
--   type is not eligible for instance search.
initialInstanceCandidates :: Type -> TCM (Maybe [Candidate])
initialInstanceCandidates t = do
  (_ , otn) <- getOutputTypeName t
  case otn of
    NoOutputTypeName -> typeError $ GenericError $
      "Instance search can only be used to find elements in a named type"
    OutputTypeNameNotYetKnown -> do
      reportSDoc "tc.instance.cands" 30 $ "Instance type is not yet known. "
      return Nothing
    OutputTypeVisiblePi -> typeError $ GenericError $
      "Instance search cannot be used to find elements in an explicit function type"
    OutputTypeVar    -> do
      reportSDoc "tc.instance.cands" 30 $ "Instance type is a variable. "
      maybeRight <$> runExceptT getContextVars
    OutputTypeName n -> do
      reportSDoc "tc.instance.cands" 30 $ "Found instance type head: " <+> prettyTCM n
      runExceptT getContextVars >>= \case
        Left b -> return Nothing
        Right ctxVars -> Just . (ctxVars ++) <$> getScopeDefs n
  where
    -- get a list of variables with their type, relative to current context
    getContextVars :: ExceptT Blocked_ TCM [Candidate]
    getContextVars = do
      ctx <- getContext
      reportSDoc "tc.instance.cands" 40 $ hang "Getting candidates from context" 2 (inTopContext $ prettyTCM $ PrettyContext ctx)
          -- Context variables with their types lifted to live in the full context
      let varsAndRaisedTypes = [ (var i, raise (i + 1) t) | (i, t) <- zip [0..] ctx ]
          vars = [ Candidate LocalCandidate x t (isOverlappable info)
                 | (x, Dom{domInfo = info, unDom = (_, t)}) <- varsAndRaisedTypes
                 , isInstance info
                 , usableModality info
                 ]

      -- {{}}-fields of variables are also candidates
      let cxtAndTypes = [ (LocalCandidate, x, t) | (x, Dom{unDom = (_, t)}) <- varsAndRaisedTypes ]
      fields <- concat <$> mapM instanceFields (reverse cxtAndTypes)
      reportSDoc "tc.instance.fields" 30 $
        if null fields then "no instance field candidates" else
          "instance field candidates" $$ do
            nest 2 $ vcat
              [ sep [ (if overlap then "overlap" else empty) <+> prettyTCM c <+> ":"
                    , nest 2 $ prettyTCM t
                    ]
              | c@(Candidate q v t overlap) <- fields
              ]

      -- get let bindings
      env <- asksTC envLetBindings
      env <- mapM (traverse getOpen) $ Map.toList env
      let lets = [ Candidate LocalCandidate v t False
                 | (_,(v, Dom{domInfo = info, unDom = t})) <- env
                 , isInstance info
                 , usableModality info
                 ]
      return $ vars ++ fields ++ lets

    etaExpand :: (MonadTCM m, MonadReduce m, HasConstInfo m, HasBuiltins m)
              => Bool -> Type -> m (Maybe (QName, Args))
    etaExpand etaOnce t =
      isEtaRecordType t >>= \case
        Nothing | etaOnce -> do
          isRecordType t >>= \case
            Nothing         -> return Nothing
            Just (r, vs, _) -> do
              m <- currentModule
              -- Are we inside the record module? If so it's safe and desirable
              -- to eta-expand once (issue #2320).
              if qnameToList r `List.isPrefixOf` mnameToList m
                then return (Just (r, vs))
                else return Nothing
        r -> return r

    instanceFields :: (CandidateKind,Term,Type) -> ExceptT Blocked_ TCM [Candidate]
    instanceFields = instanceFields' True

    instanceFields' :: Bool -> (CandidateKind,Term,Type) -> ExceptT Blocked_ TCM [Candidate]
    instanceFields' etaOnce (q, v, t) =
      ifBlocked t (\m _ -> throwError $ Blocked m ()) $ \ _ t -> do
      caseMaybeM (etaExpand etaOnce t) (return []) $ \ (r, pars) -> do
        (tel, args) <- lift $ forceEtaExpandRecord r pars v
        let types = map unDom $ applySubst (parallelS $ reverse $ map unArg args) (flattenTel tel)
        fmap concat $ forM (zip args types) $ \ (arg, t) ->
          ([ Candidate LocalCandidate (unArg arg) t (isOverlappable arg)
           | isInstance arg ] ++) <$>
          instanceFields' False (LocalCandidate, unArg arg, t)

    getScopeDefs :: QName -> TCM [Candidate]
    getScopeDefs n = do
      instanceDefs <- getInstanceDefs
      rel          <- asksTC getRelevance
      let qs = maybe [] Set.toList $ Map.lookup n instanceDefs
      catMaybes <$> mapM (candidate rel) qs

    candidate :: Relevance -> QName -> TCM (Maybe Candidate)
    candidate rel q = ifNotM (isNameInScope q <$> getScope) (return Nothing) $ do
      -- Jesper, 2020-03-16: When using --no-qualified-instances,
      -- filter out instances that are only in scope under a qualified
      -- name.
      filterQualified $ do
      -- Andreas, 2012-07-07:
      -- we try to get the info for q
      -- while opening a module, q may be in scope but not in the signature
      -- in this case, we just ignore q (issue 674)
      flip catchError handle $ do
        def <- getConstInfo q
        if not (getRelevance def `moreRelevant` rel) then return Nothing else do
          -- Andreas, 2017-01-14: instantiateDef is a bit of an overkill
          -- if we anyway get the freeVarsToApply
          -- WAS: t <- defType <$> instantiateDef def
          args <- freeVarsToApply q
          let t = defType def `piApply` args
              rel = getRelevance $ defArgInfo def
          let v = case theDef def of
               -- drop parameters if it's a projection function...
               Function{ funProjection = Just p } -> projDropParsApply p ProjSystem rel args
               -- Andreas, 2014-08-19: constructors cannot be declared as
               -- instances (at least as of now).
               -- I do not understand why the Constructor case is not impossible.
               -- Ulf, 2014-08-20: constructors are always instances.
               Constructor{ conSrcCon = c }       -> Con c ConOSystem []
               _                                  -> Def q $ map Apply args
          return $ Just $ Candidate (GlobalCandidate q) v t False
      where
        -- unbound constant throws an internal error
        handle (TypeError _ (Closure {clValue = InternalError _})) = return Nothing
        handle err                                                 = throwError err

        filterQualified :: TCM (Maybe Candidate) -> TCM (Maybe Candidate)
        filterQualified m = ifM (optQualifiedInstances <$> pragmaOptions) m $ do
          qc <- inverseScopeLookup' AmbiguousAnything (Right q) <$> getScope
          let isQual = maybe False isQualified $ listToMaybe qc
          if isQual then return Nothing else m


-- | @findInstance m (v,a)s@ tries to instantiate on of the types @a@s
--   of the candidate terms @v@s to the type @t@ of the metavariable @m@.
--   If successful, meta @m@ is solved with the instantiation of @v@.
--   If unsuccessful, the constraint is regenerated, with possibly reduced
--   candidate set.
--   The list of candidates is equal to @Nothing@ when the type of the meta
--   wasn't known when the constraint was generated. In that case, try to find
--   its type again.
findInstance :: MetaId -> Maybe [Candidate] -> TCM ()
findInstance m Nothing = do
  -- Andreas, 2015-02-07: New metas should be created with range of the
  -- current instance meta, thus, we set the range.
  mv <- lookupMeta m
  setCurrentRange mv $ do
    reportSLn "tc.instance" 20 $ "The type of the FindInstance constraint isn't known, trying to find it again."
    t <- instantiate =<< getMetaTypeInContext m
    reportSLn "tc.instance" 70 $ "findInstance 1: t: " ++ prettyShow t

    -- Issue #2577: If the target is a function type the arguments are
    -- potential candidates, so we add them to the context to make
    -- initialInstanceCandidates pick them up.
    TelV tel t <- telViewUpTo' (-1) notVisible t
    cands <- addContext tel $ initialInstanceCandidates t
    case cands of
      Nothing -> do
        reportSLn "tc.instance" 20 "Can't figure out target of instance goal. Postponing constraint."
        addConstraint $ FindInstance m Nothing Nothing
      Just {} -> findInstance m cands

findInstance m (Just cands) =
  whenJustM (findInstance' m cands) $ (\ (cands, b) -> addConstraint $ FindInstance m b $ Just cands)

-- | Result says whether we need to add constraint, and if so, the set of
--   remaining candidates and an eventual blocking metavariable.
findInstance' :: MetaId -> [Candidate] -> TCM (Maybe ([Candidate], Maybe MetaId))
findInstance' m cands = ifM (isFrozen m) (do
    reportSLn "tc.instance" 20 "Refusing to solve frozen instance meta."
    return (Just (cands, Nothing))) $ do
  ifM shouldPostponeInstanceSearch (do
    reportSLn "tc.instance" 20 "Postponing possibly recursive instance search."
    return $ Just (cands, Nothing)) $ billTo [Benchmark.Typing, Benchmark.InstanceSearch] $ do
  -- Andreas, 2015-02-07: New metas should be created with range of the
  -- current instance meta, thus, we set the range.
  mv <- lookupMeta m
  setCurrentRange mv $ do
      reportSLn "tc.instance" 15 $
        "findInstance 2: constraint: " ++ prettyShow m ++ "; candidates left: " ++ show (length cands)
      reportSDoc "tc.instance" 60 $ nest 2 $ vcat
        [ sep [ (if overlap then "overlap" else empty) <+> prettyTCM c <+> ":"
              , nest 2 $ prettyTCM t ] | c@(Candidate q v t overlap) <- cands ]
      reportSDoc "tc.instance" 70 $ "raw" $$ do
       nest 2 $ vcat
        [ sep [ (if overlap then "overlap" else empty) <+> prettyTCM c <+> ":"
              , nest 2 $ pretty t ] | c@(Candidate q v t overlap) <- cands ]
      t <- getMetaTypeInContext m
      reportSLn "tc.instance" 70 $ "findInstance 2: t: " ++ prettyShow t
      insidePi t $ \ t -> do
      reportSDoc "tc.instance" 15 $ "findInstance 3: t =" <+> prettyTCM t
      reportSLn "tc.instance" 70 $ "findInstance 3: t: " ++ prettyShow t

      mcands <- checkCandidates m t cands
      debugConstraints
      case mcands of

        Just ([(_, err)], []) -> do
          reportSDoc "tc.instance" 15 $
            "findInstance 5: the only viable candidate failed..."
          throwError err
        Just (errs, []) -> do
          if null errs then reportSDoc "tc.instance" 15 $ "findInstance 5: no viable candidate found..."
                       else reportSDoc "tc.instance" 15 $ "findInstance 5: all viable candidates failed..."
          -- #3676: Sort the candidates based on the size of the range for the errors and
          --        set the range of the full error to the range of the most precise candidate
          --        error.
          let sortedErrs = List.sortBy (compare `on` precision) errs
                where precision (_, err) = maybe infinity iLength $ rangeToInterval $ getRange err
                      infinity = 1000000000
          setCurrentRange (take 1 $ map snd sortedErrs) $
            typeError $ InstanceNoCandidate t [ (candidateTerm c, err) | (c, err) <- sortedErrs ]

        Just (_, [c@(Candidate q term t' _)]) -> do
          reportSDoc "tc.instance" 15 $ vcat
            [ "findInstance 5: solved by instance search using the only candidate"
            , nest 2 $ prettyTCM c <+> "=" <+> prettyTCM term
            , "of type " <+> prettyTCM t'
            , "for type" <+> prettyTCM t
            ]

          -- If we actually solved the constraints we should wake up any held
          -- instance constraints, to make sure we don't forget about them.
          wakeupInstanceConstraints
          return Nothing  -- We’re done

        _ -> do
          let cs = maybe cands snd mcands -- keep the current candidates if Nothing
          reportSDoc "tc.instance" 15 $
            text ("findInstance 5: refined candidates: ") <+>
            prettyTCM (List.map candidateTerm cs)
          return (Just (cs, Nothing))

insidePi :: Type -> (Type -> TCM a) -> TCM a
insidePi t ret = reduce (unEl t) >>= \case
    Pi a b     -> addContext (absName b, a) $ insidePi (absBody b) ret
    Def{}      -> ret t
    Var{}      -> ret t
    Sort{}     -> __IMPOSSIBLE__
    Con{}      -> __IMPOSSIBLE__
    Lam{}      -> __IMPOSSIBLE__
    Lit{}      -> __IMPOSSIBLE__
    Level{}    -> __IMPOSSIBLE__
    MetaV{}    -> __IMPOSSIBLE__
    DontCare{} -> __IMPOSSIBLE__
    Dummy s _  -> __IMPOSSIBLE_VERBOSE__ s

-- | Apply the computation to every argument in turn by reseting the state every
--   time. Return the list of the arguments giving the result True.
--
--   If the resulting list contains exactly one element, then the state is the
--   same as the one obtained after running the corresponding computation. In
--   all the other cases, the state is reset.
--
--   Also returns the candidates that pass type checking but fails constraints,
--   so that the error messages can be reported if there are no successful
--   candidates.
filterResetingState :: MetaId -> [Candidate] -> (Candidate -> TCM YesNoMaybe) -> TCM ([(Candidate, TCErr)], [Candidate])
filterResetingState m cands f = do
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
  result'' <- dropSameCandidates m result'
  case result'' of
    [(c, _, _, s)] -> ([], [c]) <$ putTC s
    _              -> do
      let bad  = [ (c, err) | (c, ((NoBecause err, _, _), _)) <- result ]
          good = [ c | (c, _, _, _) <- result'' ]
      return (bad, good)

-- Drop all candidates which are judgmentally equal to the first one.
-- This is sufficient to reduce the list to a singleton should all be equal.
dropSameCandidates :: MetaId -> [(Candidate, Term, Type, a)] -> TCM [(Candidate, Term, Type, a)]
dropSameCandidates m cands0 = verboseBracket "tc.instance" 30 "dropSameCandidates" $ do
  metas <- getMetaVariableSet
  -- Does `it` have any metas in the initial meta variable store?
  let freshMetas = getAny . allMetas (Any . (`IntSet.notMember` metas) . metaId)

  -- Take overlappable candidates into account
  let cands =
        case List.partition (\ (c, _, _, _) -> candidateOverlappable c) cands0 of
          (cand : _, []) -> [cand]  -- only overlappable candidates: pick the first one
          _              -> cands0  -- otherwise require equality

  reportSDoc "tc.instance" 50 $ vcat
    [ "valid candidates:"
    , nest 2 $ vcat [ if freshMetas (v, a) then "(redacted)" else
                      sep [ prettyTCM v <+> ":", nest 2 $ prettyTCM a ]
                    | (_, v, a, _) <- cands ] ]
  rel <- getMetaRelevance <$> lookupMeta m
  case cands of
    []            -> return cands
    cvd : _ | isIrrelevant rel -> do
      reportSLn "tc.instance" 30 "Meta is irrelevant so any candidate will do."
      return [cvd]
    (_, MetaV m' _, _, _) : _ | m == m' ->  -- We didn't instantiate, so can't compare
      return cands
    cvd@(_, v, a, _) : vas -> do
        if freshMetas (v, a)
          then return (cvd : vas)
          else (cvd :) <$> dropWhileM equal vas
      where
        equal (_, v', a', _)
            | freshMetas (v', a') = return False  -- If there are fresh metas we can't compare
            | otherwise           =
          verboseBracket "tc.instance" 30 "comparingCandidates" $ do
          reportSDoc "tc.instance" 30 $ sep [ prettyTCM v <+> "==", nest 2 $ prettyTCM v' ]
          localTCState $ dontAssignMetas $ ifNoConstraints_ (equalType a a' >> equalTerm a v v')
                             {- then -} (return True)
                             {- else -} (\ _ -> return False)
                             `catchError` (\ _ -> return False)

data YesNoMaybe = Yes | No | NoBecause TCErr | Maybe | HellNo TCErr
  deriving (Show)

isNo :: YesNoMaybe -> Bool
isNo No          = True
isNo NoBecause{} = True
isNo HellNo{}    = True
isNo _           = False

-- | Given a meta @m@ of type @t@ and a list of candidates @cands@,
-- @checkCandidates m t cands@ returns a refined list of valid candidates and
-- candidates that failed some constraints.
checkCandidates :: MetaId -> Type -> [Candidate] -> TCM (Maybe ([(Candidate, TCErr)], [Candidate]))
checkCandidates m t cands =
  verboseBracket "tc.instance.candidates" 20 ("checkCandidates " ++ prettyShow m) $
  ifM (anyMetaTypes cands) (return Nothing) $ Just <$> do
    reportSDoc "tc.instance.candidates" 20 $ nest 2 $ "target:" <+> prettyTCM t
    reportSDoc "tc.instance.candidates" 20 $ nest 2 $ vcat
      [ "candidates"
      , vcat [ "-" <+> (if overlap then "overlap" else empty) <+> prettyTCM c <+> ":" <+> prettyTCM t
             | c@(Candidate q v t overlap) <- cands ] ]
    cands' <- filterResetingState m cands (checkCandidateForMeta m t)
    reportSDoc "tc.instance.candidates" 20 $ nest 2 $ vcat
      [ "valid candidates"
      , vcat [ "-" <+> (if overlap then "overlap" else empty) <+> prettyTCM c <+> ":" <+> prettyTCM t
             | c@(Candidate q v t overlap) <- snd cands' ] ]
    return cands'
  where
    anyMetaTypes :: [Candidate] -> TCM Bool
    anyMetaTypes [] = return False
    anyMetaTypes (Candidate _ _ a _ : cands) = do
      a <- instantiate a
      case unEl a of
        MetaV{} -> return True
        _       -> anyMetaTypes cands

    checkDepth :: Term -> Type -> TCM YesNoMaybe -> TCM YesNoMaybe
    checkDepth c a k = locallyTC eInstanceDepth succ $ do
      d        <- viewTC eInstanceDepth
      maxDepth <- maxInstanceSearchDepth
      when (d > maxDepth) $ typeError $ InstanceSearchDepthExhausted c a maxDepth
      k

    checkCandidateForMeta :: MetaId -> Type -> Candidate -> TCM YesNoMaybe
    checkCandidateForMeta m t (Candidate q term t' _) = checkDepth term t' $ do
      -- Andreas, 2015-02-07: New metas should be created with range of the
      -- current instance meta, thus, we set the range.
      mv <- lookupMeta m
      setCurrentRange mv $ do
        debugConstraints
        verboseBracket "tc.instance" 20 ("checkCandidateForMeta " ++ prettyShow m) $
          liftTCM $ runCandidateCheck $ do
            reportSLn "tc.instance" 70 $ "  t: " ++ prettyShow t ++ "\n  t':" ++ prettyShow t' ++ "\n  term: " ++ prettyShow term ++ "."
            reportSDoc "tc.instance" 20 $ vcat
              [ "checkCandidateForMeta"
              , "t    =" <+> prettyTCM t
              , "t'   =" <+> prettyTCM t'
              , "term =" <+> prettyTCM term
              ]

            -- Apply hidden and instance arguments (recursive inst. search!).
            (args, t'') <- implicitArgs (-1) (\h -> notVisible h) t'

            reportSDoc "tc.instance" 20 $
              "instance search: checking" <+> prettyTCM t''
              <+> "<=" <+> prettyTCM t
            reportSDoc "tc.instance" 70 $ vcat
              [ "instance search: checking (raw)"
              , nest 4 $ pretty t''
              , nest 2 $ "<="
              , nest 4 $ pretty t
              ]
            v <- (`applyDroppingParameters` args) =<< reduce term
            reportSDoc "tc.instance" 15 $ vcat
              [ "instance search: attempting"
              , nest 2 $ prettyTCM m <+> ":=" <+> prettyTCM v
              ]
            reportSDoc "tc.instance" 70 $ nest 2 $
              "candidate v = " <+> pretty v
            -- if constraints remain, we abort, but keep the candidate
            -- Jesper, 05-12-2014: When we abort, we should add a constraint to
            -- instantiate the meta at a later time (see issue 1377).
            ctxElims <- map Apply <$> getContextArgs
            guardConstraint (ValueCmp CmpEq (AsTermsOf t'') (MetaV m ctxElims) v) $ leqType t'' t
            -- make a pass over constraints, to detect cases where some are made
            -- unsolvable by the assignment, but don't do this for FindInstance's
            -- to prevent loops.
            debugConstraints

            let debugSolution = verboseS "tc.instance" 15 $ do
                  sol <- instantiateFull (MetaV m ctxElims)
                  case sol of
                    MetaV m' _ | m == m' ->
                      reportSDoc "tc.instance" 15 $
                        sep [ ("instance search: maybe solution for" <+> prettyTCM m) <> ":"
                            , nest 2 $ prettyTCM v ]
                    _ ->
                      reportSDoc "tc.instance" 15 $
                        sep [ ("instance search: found solution for" <+> prettyTCM m) <> ":"
                            , nest 2 $ prettyTCM sol ]

            do solveAwakeConstraints' True
               Yes <$ debugSolution
              `catchError` (return . NoBecause)

        where
          runCandidateCheck check =
            flip catchError handle $
            nowConsideringInstance $
            ifNoConstraints check
              (\ r -> case r of
                  Yes           -> r <$ debugSuccess
                  NoBecause why -> r <$ debugConstraintFail why
                  _             -> __IMPOSSIBLE__
              )
              (\ _ r -> case r of
                  Yes           -> Maybe <$ debugInconclusive
                  NoBecause why -> r <$ debugConstraintFail why
                  _             -> __IMPOSSIBLE__
              )

          debugSuccess            = reportSLn "tc.instance" 50 "assignment successful" :: TCM ()
          debugInconclusive       = reportSLn "tc.instance" 50 "assignment inconclusive" :: TCM ()
          debugConstraintFail why = reportSDoc "tc.instance" 50 $ "candidate failed constraints:" <+> prettyTCM why
          debugTypeFail err       = reportSDoc "tc.instance" 50 $ "candidate failed type check:" <+> prettyTCM err

          hardFailure :: TCErr -> Bool
          hardFailure (TypeError _ err) =
            case clValue err of
              InstanceSearchDepthExhausted{} -> True
              _                              -> False
          hardFailure _ = False

          handle :: TCErr -> TCM YesNoMaybe
          handle err
            | hardFailure err = return $ HellNo err
            | otherwise       = No <$ debugTypeFail err

isInstanceConstraint :: Constraint -> Bool
isInstanceConstraint FindInstance{} = True
isInstanceConstraint _              = False

shouldPostponeInstanceSearch :: (ReadTCState m, HasOptions m) => m Bool
shouldPostponeInstanceSearch =
  and2M ((^. stConsideringInstance) <$> getTCState)
        (not . optOverlappingInstances <$> pragmaOptions)
  `or2M` ((^. stPostponeInstanceSearch) <$> getTCState)

nowConsideringInstance :: (ReadTCState m) => m a -> m a
nowConsideringInstance = locallyTCState stConsideringInstance $ const True

wakeupInstanceConstraints :: TCM ()
wakeupInstanceConstraints =
  unlessM shouldPostponeInstanceSearch $ do
    wakeConstraints (return . isInstance)
    solveSomeAwakeConstraints isInstance False
  where
    isInstance = isInstanceConstraint . clValue . theConstraint

postponeInstanceConstraints :: TCM a -> TCM a
postponeInstanceConstraints m =
  locallyTCState stPostponeInstanceSearch (const True) m <* wakeupInstanceConstraints

-- | To preserve the invariant that a constructor is not applied to its
--   parameter arguments, we explicitly check whether function term
--   we are applying to arguments is a unapplied constructor.
--   In this case we drop the first 'conPars' arguments.
--   See Issue670a.
--   Andreas, 2013-11-07 Also do this for projections, see Issue670b.
applyDroppingParameters :: Term -> Args -> TCM Term
applyDroppingParameters t vs = do
  let fallback = return $ t `apply` vs
  case t of
    Con c ci [] -> do
      def <- theDef <$> getConInfo c
      case def of
        Constructor {conPars = n} -> return $ Con c ci (map Apply $ drop n vs)
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
