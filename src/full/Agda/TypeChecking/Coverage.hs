{-# LANGUAGE CPP                      #-}
{-# LANGUAGE NondecreasingIndentation #-}

{-| Coverage checking, case splitting, and splitting for refine tactics.

 -}

module Agda.TypeChecking.Coverage
  ( SplitClause(..), clauseToSplitClause, fixTarget
  , Covering(..), splitClauses
  , coverageCheck
  , isCovered
  , splitClauseWithAbsurd
  , splitLast
  , splitResult
  , normaliseProjP
  ) where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans ( lift )

import Data.Either (lefts)
import qualified Data.List as List
import Data.Monoid (Any(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Traversable as Trav

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin

import Agda.TypeChecking.Rules.LHS (checkSortOfSplitVar)
import Agda.TypeChecking.Rules.LHS.Problem (allFlexVars)
import Agda.TypeChecking.Rules.LHS.Unify

import Agda.TypeChecking.Coverage.Match
import Agda.TypeChecking.Coverage.SplitTree

import Agda.TypeChecking.Conversion (tryConversion, equalType)
import Agda.TypeChecking.Datatypes (getConForm)
import {-# SOURCE #-} Agda.TypeChecking.Empty (isEmptyTel)
import Agda.TypeChecking.Irrelevance (applyRelevanceToContext)
import Agda.TypeChecking.Patterns.Internal (dotPatternsToPatterns)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Records
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Warnings

import Agda.Interaction.Options

import Agda.Utils.Either
import Agda.Utils.Except
  ( ExceptT
  , MonadError(catchError, throwError)
  , runExceptT
  )
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.Lens

#include "undefined.h"
import Agda.Utils.Impossible

data SplitClause = SClause
  { scTel    :: Telescope
    -- ^ Type of variables in @scPats@.
  , scPats   :: [NamedArg SplitPattern]
    -- ^ The patterns leading to the currently considered branch of
    --   the split tree.
  , scSubst  :: Substitution' SplitPattern
    -- ^ Substitution from 'scTel' to old context.
    --   Only needed directly after split on variable:
    --   * To update 'scTarget'
    --   * To rename other split variables when splitting on
    --     multiple variables.
    --   @scSubst@ is not ``transitive'', i.e., does not record
    --   the substitution from the original context to 'scTel'
    --   over a series of splits.  It is freshly computed
    --   after each split by 'computeNeighborhood'; also
    --   'splitResult', which does not split on a variable,
    --   should reset it to the identity 'idS', lest it be
    --   applied to 'scTarget' again, leading to Issue 1294.
  , scCheckpoints :: Map CheckpointId Substitution
    -- ^ We need to keep track of the module parameter checkpoints for the
    -- clause for the purpose of inferring missing instance clauses.
  , scTarget :: Maybe (Arg Type)
    -- ^ The type of the rhs, living in context 'scTel'.
    --   This invariant is broken before calls to 'fixTarget';
    --   there, 'scTarget' lives in the old context.
    --   'fixTarget' moves 'scTarget' to the new context by applying
    --   substitution 'scSubst'.
  }

-- | A @Covering@ is the result of splitting a 'SplitClause'.
data Covering = Covering
  { covSplitArg     :: Arg Nat
     -- ^ De Bruijn level (counting dot patterns) of argument we split on.
  , covSplitClauses :: [(SplitTag, SplitClause)]
      -- ^ Covering clauses, indexed by constructor/literal these clauses share.
  }

-- | Project the split clauses out of a covering.
splitClauses :: Covering -> [SplitClause]
splitClauses (Covering _ qcs) = map snd qcs

-- | Create a split clause from a clause in internal syntax. Used by make-case.
clauseToSplitClause :: Clause -> SplitClause
clauseToSplitClause cl = SClause
  { scTel    = clauseTel  cl
  , scPats   = toSplitPatterns $ namedClausePats cl
  , scSubst  = idS  -- Andreas, 2014-07-15  TODO: Is this ok?
  , scCheckpoints = Map.empty -- #2996: not __IMPOSSIBLE__ for debug printing
  , scTarget = clauseType cl
  }

type CoverM = ExceptT SplitError TCM

-- | Top-level function for checking pattern coverage.
--
--   Effects:
--
--   - Marks unreachable clauses as such in the signature.
--
--   - Adds missing instances clauses to the signature.
--
coverageCheck :: QName -> Type -> [Clause] -> TCM SplitTree
coverageCheck f t cs = do
  reportSLn "tc.cover.top" 30 $ "entering coverageCheck for " ++ show f
  TelV gamma a <- telViewUpToPath (-1) t
  reportSLn "tc.cover.top" 30 $ "coverageCheck: computed telView"

  let -- n             = arity
      -- xs            = variable patterns fitting lgamma
      n            = size gamma
      xs           =  map (setOrigin Inserted) $ teleNamedArgs gamma

  reportSLn "tc.cover.top" 30 $ "coverageCheck: getDefFreeVars"

      -- The initial module parameter substitutions need to be weakened by the
      -- number of arguments that aren't module parameters.
  fv           <- getDefFreeVars f

  reportSLn "tc.cover.top" 30 $ "coverageCheck: getting checkpoints"

  -- TODO: does this make sense? Why are we weakening by n - fv?
  checkpoints <- applySubst (raiseS (n - fv)) <$> viewTC eCheckpoints

      -- construct the initial split clause
  let sc = SClause gamma xs idS checkpoints $ Just $ defaultArg a

  reportSDoc "tc.cover.top" 10 $ do
    let prCl cl = addContext (clauseTel cl) $
                  prettyTCMPatternList $ namedClausePats cl
    vcat
      [ text $ "Coverage checking " ++ prettyShow f ++ " with patterns:"
      , nest 2 $ vcat $ map prCl cs
      ]

  -- used = actually used clauses for cover
  -- pss  = uncovered cases
  CoverResult splitTree used pss noex <- cover f cs sc
  reportSDoc "tc.cover.top" 10 $ vcat
    [ "cover computed!"
    , text $ "used clauses: " ++ show used
    , text $ "non-exact clauses: " ++ show noex
    ]
  reportSDoc "tc.cover.splittree" 10 $ vcat
    [ "generated split tree for" <+> prettyTCM f
    , text $ prettyShow splitTree
    ]

  -- filter out the missing clauses that are absurd.
  pss <- flip filterM pss $ \(tel,_) -> not <$> isEmptyTel tel

  -- report a warning if there are uncovered cases,
  -- generate a catch-all clause with a metavariable as its body to avoid
  -- internal errors in the reduction machinery.
  unless (null pss) $
      setCurrentRange cs $
        warning $ CoverageIssue f pss

  -- Andreas, 2017-08-28, issue #2723:
  -- Mark clauses as reachable or unreachable in the signature.
  let (is0, cs1) = unzip $ for (zip [0..] cs) $ \ (i, cl) ->
        let unreachable = i `Set.notMember` used in
        (boolToMaybe unreachable i, cl { clauseUnreachable = Just unreachable  })
  -- is = indices of unreachable clauses
  let is = catMaybes is0
  reportSDoc "tc.cover.top" 10 $ vcat
    [ text $ "unreachable clauses: " ++ if null is then "(none)" else show is
    ]
  -- Replace the first clauses by @cs1@.  There might be more
  -- added by @inferMissingClause@.
  modifyFunClauses f $ \ cs0 -> cs1 ++ drop (length cs1) cs0

  -- Warn if there are unreachable clauses and mark them as unreachable.
  unless (null is) $ do
    -- Warn about unreachable clauses.
    let unreached = filter ((Just True ==) . clauseUnreachable) cs1
    setCurrentRange (map clauseFullRange unreached) $
      warning $ UnreachableClauses f $ map namedClausePats unreached

  -- report a warning if there are clauses that are not preserved as
  -- definitional equalities and --exact-split is enabled
  unless (null noex) $ do
      let noexclauses = map (cs1 !!) $ Set.toList noex
      setCurrentRange (map clauseLHSRange noexclauses) $
        warning $ CoverageNoExactSplit f $ noexclauses
  return splitTree

-- | Top-level function for eliminating redundant clauses in the interactive
--   case splitter
isCovered :: QName -> [Clause] -> SplitClause -> TCM Bool
isCovered f cs sc = do
  CoverResult { coverMissingClauses = missing } <- cover f cs sc
  return $ null missing

data CoverResult = CoverResult
  { coverSplitTree       :: SplitTree
  , coverUsedClauses     :: Set Nat
  , coverMissingClauses  :: [(Telescope, [NamedArg DeBruijnPattern])]
  , coverNoExactClauses  :: Set Nat
  }

-- | @cover f cs (SClause _ _ ps _) = return (splitTree, used, pss)@.
--   checks that the list of clauses @cs@ covers the given split clause.
--   Returns the @splitTree@, the @used@ clauses, and missing cases @pss@.
--
--   Effect: adds missing instance clauses for @f@ to signature.
--
cover :: QName -> [Clause] -> SplitClause ->
         TCM CoverResult
cover f cs sc@(SClause tel ps _ _ target) = updateRelevance $ do
  reportSDoc "tc.cover.cover" 10 $ inTopContext $ vcat
    [ "checking coverage of pattern:"
    , nest 2 $ "tel  =" <+> prettyTCM tel
    , nest 2 $ "ps   =" <+> do addContext tel $ prettyTCMPatternList $ fromSplitPatterns ps
    ]
  reportSDoc "tc.cover.cover" 60 $ vcat
    [ nest 2 $ "ps   =" <+> pretty ps
    ]
  cs' <- normaliseProjP cs
  ps <- (traverse . traverse . traverse) dotPatternsToPatterns ps
  case match cs' ps of
    Yes (i,mps) -> do
      exact <- allM mps isTrivialPattern
      let noExactClause = if exact || clauseCatchall (cs !! i)
                          then Set.empty
                          else Set.singleton i
      reportSLn "tc.cover.cover" 10 $ "pattern covered by clause " ++ show i
      return $ CoverResult (SplittingDone (size tel)) (Set.singleton i) [] noExactClause

    No        ->  do
      reportSLn "tc.cover" 20 $ "pattern is not covered"
      case fmap getHiding target of
        Just h | isInstance h -> do
          -- Ulf, 2016-10-31: For now we only infer instance clauses. It would
          -- make sense to do it also for hidden, but since the value of a
          -- hidden clause is expected to be forced by later clauses, it's too
          -- late to add it now. If it was inferrable we would have gotten a
          -- type error before getting to this point.
          inferMissingClause f sc
          return $ CoverResult (SplittingDone (size tel)) Set.empty [] Set.empty
        _ -> do
          let ps' = fromSplitPatterns ps
          return $ CoverResult (SplittingDone (size tel)) Set.empty [(tel, ps')] Set.empty

    -- We need to split!
    -- If all clauses have an unsplit copattern, we try that first.
    Block res bs -> tryIf res splitRes $ do
      let ps' = fromSplitPatterns ps
          done = return $ CoverResult (SplittingDone (size tel)) Set.empty [(tel, ps')] Set.empty
      if null bs then done else do
      -- Otherwise, if there are variables to split, we try them
      -- in the order determined by a split strategy.
      reportSLn "tc.cover.strategy" 20 $ "blocking vars = " ++ prettyShow bs
      -- xs is a non-empty lists of blocking variables
      -- try splitting on one of them
      xs <- splitStrategy bs tel
      -- Andreas, 2017-10-08, issue #2594
      -- First, try to find split order for complete coverage.
      -- If this fails, try to at least carry out the splitting to the end.
      continue xs NoAllowPartialCover $ \ _err -> do
        continue xs YesAllowPartialCover $ \ err -> do
          typeError $ SplitError err
  where
    updateRelevance :: TCM a -> TCM a
    updateRelevance cont = do
      let rel = caseMaybe target Relevant $ \b ->
                  if isProp (unArg b)
                  then Irrelevant
                  else getRelevance b
      applyRelevanceToContext rel cont

    continue
      :: [BlockingVar]
      -> AllowPartialCover
      -> (SplitError -> TCM CoverResult)
      -> TCM CoverResult
    continue xs allowPartialCover handle = do
      r <- altM1 (split Inductive allowPartialCover sc) xs
      case r of
        Left err -> handle err
        -- If we get the empty covering, we have reached an impossible case
        -- and are done.
        Right (Covering n []) ->
          return $ CoverResult (SplittingDone (size tel)) Set.empty [] Set.empty
        Right (Covering n scs) -> do
          results <- mapM (cover f cs) (map snd scs)
          let trees = map coverSplitTree results
              useds = map coverUsedClauses results
              psss  = map coverMissingClauses results
              noex  = map coverNoExactClauses results
          -- Jesper, 2016-03-10  We need to remember which variables were
          -- eta-expanded by the unifier in order to generate a correct split
          -- tree (see Issue 1872).
          reportSDoc "tc.cover.split.eta" 60 $ vcat
            [ "etaRecordSplits"
            , nest 2 $ vcat
              [ "n   = " <+> text (show n)
              , "scs = " <+> prettyTCM scs
              , "ps  = " <+> text (show ps)
              ]
            ]
          let trees' = zipWith (etaRecordSplits (unArg n) ps) scs trees
              tree   = SplitAt n trees'
          return $ CoverResult tree (Set.unions useds) (concat psss) (Set.unions noex)

    tryIf :: Monad m => Bool -> m (Either err a) -> m a -> m a
    tryIf True  me m = fromRightM (const m) me
    tryIf False me m = m

    -- Try to split result
    splitRes :: TCM (Either CosplitError CoverResult)
    splitRes = do
      reportSLn "tc.cover" 20 $ "blocked by projection pattern"
      -- forM is a monadic map over a Maybe here
      mcov <- splitResult f sc
      Trav.forM mcov $ \ (Covering n scs) -> do
        -- If result splitting was successful, continue coverage checking.
        (projs, results) <- unzip <$> do
          mapM (traverseF $ cover f cs <=< (snd <.> fixTarget)) scs
          -- OR:
          -- forM scs $ \ (proj, sc') -> (proj,) <$> do
          --   cover f cs =<< do
          --     snd <$> fixTarget sc'
        let trees = map coverSplitTree results
            useds = map coverUsedClauses results
            psss  = map coverMissingClauses results
            noex  = map coverNoExactClauses results
            tree  = SplitAt n $ zip projs trees
        return $ CoverResult tree (Set.unions useds) (concat psss) (Set.unions noex)

    gatherEtaSplits :: Int -> SplitClause
                    -> [NamedArg SplitPattern] -> [NamedArg SplitPattern]
    gatherEtaSplits n sc []
       | n >= 0    = __IMPOSSIBLE__ -- we should have encountered the main
                                    -- split by now already
       | otherwise = []
    gatherEtaSplits n sc (p:ps) = case namedArg p of
      VarP _ x
       | n == 0    -> case p' of -- this is the main split
           VarP  _ _    -> p : gatherEtaSplits (-1) sc ps
           DotP  _ _    -> __IMPOSSIBLE__
           ConP  _ _ qs -> qs ++ gatherEtaSplits (-1) sc ps
           LitP  _      -> gatherEtaSplits (-1) sc ps
           ProjP{}      -> __IMPOSSIBLE__
       | otherwise ->
           updateNamedArg (\ _ -> p') p : gatherEtaSplits (n-1) sc ps
        where p' = lookupS (scSubst sc) $ splitPatVarIndex x
      DotP  _ _    -> p : gatherEtaSplits (n-1) sc ps -- count dot patterns
      ConP  _ _ qs -> gatherEtaSplits n sc (qs ++ ps)
      LitP  _      -> gatherEtaSplits n sc ps
      ProjP{}      -> gatherEtaSplits n sc ps

    addEtaSplits :: Int -> [NamedArg SplitPattern] -> SplitTree -> SplitTree
    addEtaSplits k []     t = t
    addEtaSplits k (p:ps) t = case namedArg p of
      VarP  _ _     -> addEtaSplits (k+1) ps t
      DotP  _ _     -> addEtaSplits (k+1) ps t
      ConP c cpi qs -> SplitAt (p $> k) [(SplitCon (conName c) , addEtaSplits k (qs ++ ps) t)]
      LitP  _       -> __IMPOSSIBLE__
      ProjP{}       -> __IMPOSSIBLE__

    etaRecordSplits :: Int -> [NamedArg SplitPattern] -> (SplitTag,SplitClause)
                    -> SplitTree -> (SplitTag,SplitTree)
    etaRecordSplits n ps (q , sc) t =
      (q , addEtaSplits 0 (gatherEtaSplits n sc ps) t)

-- | Append a instance clause to the clauses of a function.
inferMissingClause
  :: QName
       -- ^ Function name.
  -> SplitClause
       -- ^ Clause to add.  Clause hiding (in 'clauseType') must be 'Instance'.
   -> TCM ()
inferMissingClause f (SClause tel ps _ cps (Just t)) = setCurrentRange f $ do
  reportSDoc "tc.cover.infer" 20 $ addContext tel $ "Trying to infer right-hand side of type" <+> prettyTCM t
  cl <- addContext tel
        $ locallyTC eCheckpoints (const cps)
        $ checkpoint IdS $ do    -- introduce a fresh checkpoint
    (_x, rhs) <- case getHiding t of
                  Instance{} -> newIFSMeta "" (unArg t)
                  Hidden     -> __IMPOSSIBLE__
                  NotHidden  -> __IMPOSSIBLE__
    return $ Clause { clauseLHSRange  = noRange
                    , clauseFullRange = noRange
                    , clauseTel       = tel
                    , namedClausePats = fromSplitPatterns ps
                    , clauseBody      = Just rhs
                    , clauseType      = Just t
                    , clauseCatchall  = False
                    , clauseUnreachable = Just False  -- missing, thus, not unreachable
                    }
  addClauses f [cl]  -- Important: add at the end.
inferMissingClause _ (SClause _ _ _ _ Nothing) = __IMPOSSIBLE__

splitStrategy :: BlockingVars -> Telescope -> TCM BlockingVars
splitStrategy bs tel = return $ updateLast setBlockingVarOverlap xs
  -- Make sure we do not insists on precomputed coverage when
  -- we make our last try to split.
  -- Otherwise, we will not get a nice error message.
  where
    xs       = bs
{- KEEP!
--  Andreas, 2012-10-13
--  The following split strategy which prefers all-constructor columns
--  fails on test/fail/CoverStrategy
    xs       = ys ++ zs
    (ys, zs) = partition allConstructors bs
    allConstructors :: BlockingVar -> Bool
    allConstructors = isJust . snd
-}

-- | Check that a type is a non-irrelevant datatype or a record with
-- named constructor. Unless the 'Induction' argument is 'CoInductive'
-- the data type must be inductive.
isDatatype :: (MonadTCM tcm, MonadError SplitError tcm) =>
              Induction -> Dom Type ->
              tcm (DataOrRecord, QName, [Arg Term], [Arg Term], [QName])
isDatatype ind at = do
  let t       = unDom at
      throw f = throwError . f =<< do liftTCM $ buildClosure t
  t' <- liftTCM $ reduce t
  mInterval <- liftTCM $ getBuiltinName' builtinInterval
  case unEl t' of
    Def d [] | Just d == mInterval -> throw NotADatatype
    Def d es -> do
      let ~(Just args) = allApplyElims es
      def <- liftTCM $ theDef <$> getConstInfo d
      case def of
        Datatype{dataPars = np, dataCons = cs, dataInduction = i}
          | i == CoInductive && ind /= CoInductive ->
              throw CoinductiveDatatype
          | otherwise -> do
              let (ps, is) = splitAt np args
              return (IsData, d, ps, is, cs)
        Record{recPars = np, recConHead = con, recInduction = i}
          | i == Just CoInductive && ind /= CoInductive ->
              throw CoinductiveDatatype
          | otherwise ->
              return (IsRecord, d, args, [], [conName con])
        _ -> throw NotADatatype
    _ -> throw NotADatatype

-- | Update the target type, add more patterns to split clause
--   if target becomes a function type.
--   Returns the domains of the function type (if any).
fixTarget :: SplitClause -> TCM (Telescope, SplitClause)
fixTarget sc@SClause{ scTel = sctel, scPats = ps, scSubst = sigma, scCheckpoints = cps, scTarget = target } =
  caseMaybe target (return (empty, sc)) $ \ a -> do
    reportSDoc "tc.cover.target" 20 $ sep
      [ "split clause telescope: " <+> prettyTCM sctel
      , "old patterns          : " <+> do
          addContext sctel $ prettyTCMPatternList $ fromSplitPatterns ps
      ]
    reportSDoc "tc.cover.target" 60 $ sep
      [ "substitution          : " <+> text (show sigma)
      ]
    reportSDoc "tc.cover.target" 30 $ sep
      [ "target type before substitution (variables may be wrong): " <+> do
          addContext sctel $ prettyTCM a
      ]
    TelV tel b <- telViewUpToPath (-1) $ applySplitPSubst sigma $ unArg a
    reportSDoc "tc.cover.target" 15 $ sep
      [ "target type telescope (after substitution): " <+> do
          addContext sctel $ prettyTCM tel
      , "target type core      (after substitution): " <+> do
          addContext sctel $ addContext tel $ prettyTCM b
      ]
    let n         = size tel
        -- Andreas, 2016-10-04 issue #2236
        -- Need to set origin to "Inserted" to avoid printing of hidden patterns.
        xs        = map (mapArgInfo hiddenInserted) $ teleNamedArgs tel
        -- Compute new split clause
        sctel'    = telFromList $ telToList (raise n sctel) ++ telToList tel
        -- Dot patterns in @ps@ need to be raised!  (Issue 1298)
        ps'       = applySubst (raiseS n) ps ++ xs
        newTarget = Just $ a $> b
        sc'       = SClause
          { scTel    = sctel'
          , scPats   = ps'
          , scSubst  = wkS n $ sigma -- Should be wkS instead of liftS since
                                     -- variables are only added to new tel.
          , scCheckpoints        = applySubst (raiseS n) cps
          , scTarget = newTarget
          }
    -- Separate debug printing to find cause of crash (Issue 1374)
    reportSDoc "tc.cover.target" 30 $ sep
      [ "new split clause telescope   : " <+> prettyTCM sctel'
      ]
    reportSDoc "tc.cover.target" 30 $ sep
      [ "new split clause patterns    : " <+> do
          addContext sctel' $ prettyTCMPatternList $ fromSplitPatterns ps'
      ]
    reportSDoc "tc.cover.target" 60 $ sep
      [ "new split clause substitution: " <+> text (show $ scSubst sc')
      ]
    reportSDoc "tc.cover.target" 30 $ sep
      [ "new split clause target      : " <+> do
          addContext sctel' $ prettyTCM $ fromJust newTarget
      ]
    reportSDoc "tc.cover.target" 20 $ sep
      [ "new split clause"
      , prettyTCM sc'
      ]
    return $ if n == 0 then (empty, sc { scTarget = newTarget }) else (tel, sc')

-- Andreas, 2017-01-18, issue #819, set visible arguments to UserWritten.
-- Otherwise, they will be printed as _.
hiddenInserted :: ArgInfo -> ArgInfo
hiddenInserted ai
  | visible ai = setOrigin UserWritten ai
  | otherwise  = setOrigin Inserted ai

-- | @computeNeighbourhood delta1 delta2 d pars ixs hix tel ps con@
--
--   @
--      delta1   Telescope before split point
--      n        Name of pattern variable at split point
--      delta2   Telescope after split point
--      d        Name of datatype to split at
--      pars     Data type parameters
--      ixs      Data type indices
--      hix      Index of split variable
--      tel      Telescope for patterns ps
--      ps       Patterns before doing the split
--      cps      Current module parameter checkpoints
--      con      Constructor to fit into hole
--   @
--   @dtype == d pars ixs@
computeNeighbourhood
  :: Telescope                    -- ^ Telescope before split point.
  -> PatVarName                   -- ^ Name of pattern variable at split point.
  -> Telescope                    -- ^ Telescope after split point.
  -> QName                        -- ^ Name of datatype to split at.
  -> Args                         -- ^ Data type parameters.
  -> Args                         -- ^ Data type indices.
  -> Nat                          -- ^ Index of split variable.
  -> Telescope                    -- ^ Telescope for the patterns.
  -> [NamedArg SplitPattern]      -- ^ Patterns before doing the split.
  -> Map CheckpointId Substitution -- ^ Current checkpoints
  -> QName                        -- ^ Constructor to fit into hole.
  -> CoverM (Maybe SplitClause)   -- ^ New split clause if successful.
computeNeighbourhood delta1 n delta2 d pars ixs hix tel ps cps c = do

  -- Get the type of the datatype
  dtype <- liftTCM $ (`piApply` pars) . defType <$> getConstInfo d

  -- Get the real constructor name
  con <- liftTCM $ fromRight __IMPOSSIBLE__ <$> getConForm c
  con <- return $ con { conName = c }  -- What if we restore the current name?
                                       -- Andreas, 2013-11-29 changes nothing!

  -- Get the type of the constructor
  ctype <- liftTCM $ defType <$> getConInfo con

  -- Lookup the type of the constructor at the given parameters
  (gamma0, cixs) <- do
    TelV gamma0 (El _ d) <- liftTCM $ telView (ctype `piApply` pars)
    let Def _ es = d
        Just cixs = allApplyElims es
    return (gamma0, cixs)

  -- Andreas, 2012-02-25 preserve name suggestion for recursive arguments
  -- of constructor

  let preserve (x, t@(El _ (Def d' _))) | d == d' = (n, t)
      preserve (x, t) = (x, t)
      gammal = map (fmap preserve) . telToList $ gamma0
      gamma  = telFromList gammal
      delta1Gamma = delta1 `abstract` gamma

  debugInit con ctype d pars ixs cixs delta1 delta2 gamma tel ps hix

  -- All variables are flexible
  let flex = allFlexVars delta1Gamma

  -- Unify constructor target and given type (in Δ₁Γ)
  let conIxs   = drop (size pars) cixs
      givenIxs = raise (size gamma) ixs

  r <- unifyIndices
         delta1Gamma
         flex
         (raise (size gamma) dtype)
         conIxs
         givenIxs

  case r of
    NoUnify {} -> debugNoUnify $> Nothing

    DontKnow errs -> do
      debugCantSplit
      throwError $ UnificationStuck (conName con) (delta1 `abstract` gamma) conIxs givenIxs errs
    Unifies (delta1',rho0,_) -> do
      debugSubst "rho0" rho0

      -- We have Δ₁' ⊢ ρ₀ : Δ₁Γ, so split it into the part for Δ₁ and the part for Γ
      let (rho1,rho2) = splitS (size gamma) $ toSplitPSubst rho0

      -- Andreas, 2015-05-01  I guess it is fine to use no @conPType@
      -- as the result of splitting is never used further down the pipeline.
      -- After splitting, Agda reloads the file.
      -- Andreas, 2017-09-03, issue #2729: remember that pattern was generated by case split.
      let cpi  = noConPatternInfo{ conPRecord = Just PatOSplit }
          conp = ConP con cpi $ applySubst rho2 $
                   map (mapArgInfo hiddenInserted) $ tele2NamedArgs gamma0 gamma
          -- Andreas, 2016-09-08, issue #2166: use gamma0 for correct argument names

      -- Compute final context and substitution
      let rho3    = consS conp rho1            -- Δ₁' ⊢ ρ₃ : Δ₁(x:D)
          delta2' = applySplitPSubst rho3 delta2  -- Δ₂' = Δ₂ρ₃
          delta'  = delta1' `abstract` delta2' -- Δ'  = Δ₁'Δ₂'
          rho     = liftS (size delta2) rho3   -- Δ' ⊢ ρ : Δ₁(x:D)Δ₂

      debugTel "delta'" delta'
      debugSubst "rho" rho
      debugPs tel ps

      -- Apply the substitution
      let ps' = applySubst rho ps
      debugPlugged delta' ps'

      let cps' = applySplitPSubst rho cps

      return $ Just $ SClause delta' ps' rho cps' Nothing -- target fixed later

  where
    debugInit con ctype d pars ixs cixs delta1 delta2 gamma tel ps hix =
      liftTCM $ reportSDoc "tc.cover.split.con" 20 $ vcat
        [ "computeNeighbourhood"
        , nest 2 $ vcat
          [ "context=" <+> (inTopContext . prettyTCM =<< getContextTelescope)
          , "con    =" <+> prettyTCM con
          , "ctype  =" <+> prettyTCM ctype
          , "ps     =" <+> do inTopContext $ addContext tel $ prettyTCMPatternList $ fromSplitPatterns ps
          , "d      =" <+> prettyTCM d
          , "pars   =" <+> do prettyList $ map prettyTCM pars
          , "ixs    =" <+> do addContext delta1 $ prettyList $ map prettyTCM ixs
          , "cixs   =" <+> do addContext gamma  $ prettyList $ map prettyTCM cixs
          , "delta1 =" <+> do inTopContext $ prettyTCM delta1
          , "delta2 =" <+> do inTopContext $ addContext delta1 $ addContext gamma $ prettyTCM delta2
          , "gamma  =" <+> do inTopContext $ addContext delta1 $ prettyTCM gamma
          , "hix    =" <+> text (show hix)
          ]
        ]

    debugNoUnify =
      liftTCM $ reportSLn "tc.cover.split.con" 20 "  Constructor impossible!"

    debugCantSplit =
      liftTCM $ reportSLn "tc.cover.split.con" 20 "  Bad split!"

    debugSubst s sub =
      liftTCM $ reportSDoc "tc.cover.split.con" 20 $ nest 2 $ vcat
        [ text (s ++ " =") <+> prettyTCM sub
        ]

    debugTel s tel =
      liftTCM $ reportSDoc "tc.cover.split.con" 20 $ nest 2 $ vcat
        [ text (s ++ " =") <+> prettyTCM tel
        ]

    debugPs tel ps =
      liftTCM $ reportSDoc "tc.cover.split.con" 20 $
        inTopContext $ addContext tel $ nest 2 $ vcat
          [ "ps     =" <+> prettyTCMPatternList (fromSplitPatterns ps)
          ]

    debugPlugged delta' ps' =
      liftTCM $ reportSDoc "tc.cover.split.con" 20 $
        inTopContext $ addContext delta' $ nest 2 $ vcat
          [ "ps'    =" <+> do prettyTCMPatternList $ fromSplitPatterns ps'
          ]

-- | Introduce trailing pattern variables via 'fixTarget'?
data FixTarget
  = YesFixTarget
  | NoFixTarget
  deriving (Show)

-- | Allow partial covering for split?
data AllowPartialCover
  = YesAllowPartialCover  -- To try to coverage-check incomplete splits.
  | NoAllowPartialCover   -- Default.
  deriving (Eq, Show)

-- | Entry point from @Interaction.MakeCase@.
splitClauseWithAbsurd :: SplitClause -> Nat -> TCM (Either SplitError (Either SplitClause Covering))
splitClauseWithAbsurd c x = split' Inductive NoAllowPartialCover NoFixTarget c (BlockingVar x [] [] True)
  -- Andreas, 2016-05-03, issue 1950:
  -- Do not introduce trailing pattern vars after split,
  -- because this does not work for with-clauses.

-- | Entry point from @TypeChecking.Empty@ and @Interaction.BasicOps@.
--   @splitLast CoInductive@ is used in the @refine@ tactics.

splitLast :: Induction -> Telescope -> [NamedArg DeBruijnPattern] -> TCM (Either SplitError Covering)
splitLast ind tel ps = split ind NoAllowPartialCover sc (BlockingVar 0 [] [] True)
  where sc = SClause tel (toSplitPatterns ps) empty empty Nothing

-- | @split ind splitClause x = return res@
--   splits @splitClause@ at pattern var @x@ (de Bruijn index).
--
--   Possible results @res@ are:
--
--   1. @Left err@:
--      Splitting failed.
--
--   2. @Right covering@:
--      A covering set of split clauses, one for each valid constructor.
--      This could be the empty set (denoting an absurd clause).

split :: Induction
         -- ^ Coinductive constructors are allowed if this argument is
         -- 'CoInductive'.
      -> AllowPartialCover
         -- ^ Don't fail if computed 'Covering' does not cover all constructors.
      -> SplitClause
      -> BlockingVar
      -> TCM (Either SplitError Covering)
split ind allowPartialCover sc x =
  fmap blendInAbsurdClause <$> split' ind allowPartialCover YesFixTarget sc x
  where
    n = lookupPatternVar sc $ blockingVarNo x
    blendInAbsurdClause :: Either SplitClause Covering -> Covering
    blendInAbsurdClause = fromRight (const $ Covering n [])

-- | Convert a de Bruijn index relative to the clause telescope to a de Bruijn
--   level. The result should be the argument position (counted from left,
--   starting with 0) to split at (dot patterns included!).
lookupPatternVar :: SplitClause -> Int -> Arg Nat
lookupPatternVar SClause{ scTel = tel, scPats = pats } x = arg $>
    if n < 0 then __IMPOSSIBLE__ else n
  where n = if k < 0
            then __IMPOSSIBLE__
            else fromMaybe __IMPOSSIBLE__ $ permPicks perm !!! k
        perm = fromMaybe __IMPOSSIBLE__ $ dbPatPerm $ fromSplitPatterns pats
        k = size tel - x - 1
        arg = telVars (size tel) tel !! k

-- | @split' ind splitClause x = return res@
--   splits @splitClause@ at pattern var @x@ (de Bruijn index).
--
--   Possible results @res@ are:
--
--   1. @Left err@:
--      Splitting failed.
--
--   2. @Right (Left splitClause')@:
--      Absurd clause (type of @x@ has 0 valid constructors).
--
--   3. @Right (Right covering)@:
--      A covering set of split clauses, one for each valid constructor.

split' :: Induction
          -- ^ Coinductive constructors are allowed if this argument is
          -- 'CoInductive'.
       -> AllowPartialCover
          -- ^ Don't fail if computed 'Covering' does not cover all constructors.
       -> FixTarget
          -- ^ If 'YesFixTarget', introduce new trailing variable patterns via
          --   'fixTarget'.
       -> SplitClause
       -> BlockingVar
       -> TCM (Either SplitError (Either SplitClause Covering))
split' ind allowPartialCover fixtarget sc@(SClause tel ps _ cps target) (BlockingVar x pcons' plits overlap) =
 liftTCM $ runExceptT $ do
  debugInit tel x ps cps

  -- Split the telescope at the variable
  -- t = type of the variable,  Δ₁ ⊢ t
  (n, t, delta1, delta2) <- do
    let (tel1, dom : tel2) = splitAt (size tel - x - 1) $ telToList tel
    return (fst $ unDom dom, snd <$> dom, telFromList tel1, telFromList tel2)

  -- Compute the neighbourhoods for the constructors
  let computeNeighborhoods = do
        -- Check that t is a datatype or a record
        -- Andreas, 2010-09-21, isDatatype now directly throws an exception if it fails
        -- cons = constructors of this datatype
        (dr, d, pars, ixs, cons) <- inContextOfT $ isDatatype ind t
        mns <- forM cons $ \ con -> fmap (SplitCon con,) <$>
          computeNeighbourhood delta1 n delta2 d pars ixs x tel ps cps con
        return (dr , catMaybes mns)

      computeLitNeighborhoods = do
        typeOk <- liftTCM $ do
          t' <- litType $ headWithDefault {-'-} __IMPOSSIBLE__ plits
          liftTCM $ dontAssignMetas $ tryConversion $ equalType (unDom t) t'
        unless typeOk $ throwError . NotADatatype =<< do liftTCM $ buildClosure (unDom t)
        ns <- forM plits $ \lit -> do
          let delta2' = subst 0 (Lit lit) delta2
              delta'  = delta1 `abstract` delta2'
              rho     = liftS x $ consS (LitP lit) idS
              ps'     = applySubst rho ps
              cps'    = applySplitPSubst rho cps
          return (SplitLit lit , SClause delta' ps' rho cps' Nothing)
        ca <- do
          let delta' = tel -- telescope is unchanged for catchall branch
              varp   = VarP PatOSplit $ SplitPatVar
                         { splitPatVarName   = underscore
                         , splitPatVarIndex  = 0
                         , splitExcludedLits = plits
                         }
              rho    = liftS x $ consS varp $ raiseS 1
              ps'    = applySubst rho ps
          return (SplitCatchall , SClause delta' ps' rho cps Nothing)
        return (IsData , ns ++ [ ca ])

  (dr, ns) <- if null pcons' && not (null plits)
        then computeLitNeighborhoods
        else computeNeighborhoods

  ns <- case fixtarget of
    NoFixTarget  -> return ns
    YesFixTarget -> lift $ forM ns $ \(con,sc) ->
      (con,) . snd <$> fixTarget sc{ scTarget = target }

  case ns of
    []  -> do
      let absurdp = VarP PatOAbsurd $ SplitPatVar underscore 0 []
          rho = liftS x $ consS absurdp $ raiseS 1
          ps' = applySubst rho ps
      return $ Left $ SClause
               { scTel  = tel
               , scPats = ps'
               , scSubst              = __IMPOSSIBLE__ -- not used
               , scCheckpoints        = __IMPOSSIBLE__ -- not used
               , scTarget             = Nothing
               }

    -- Jesper, 2018-05-24: If the datatype is in Prop we can
    -- only do empty splits, unless the target is in Prop too.
    (_ : _) | dr == IsData && isProp t && not (isIrrelevant relTarget) ->
      throwError . IrrelevantDatatype =<< do liftTCM $ inContextOfT $ buildClosure (unDom t)

  -- Andreas, 2012-10-10 fail if precomputed constructor set does not cover
  -- all the data type constructors
  -- Andreas, 2017-10-08 ... unless partial covering is explicitly allowed.
    _ | allowPartialCover == NoAllowPartialCover,
        overlap == False,
        let ptags = map (SplitCon . conName) pcons' ++ map SplitLit plits,
        let tags  = map fst ns,
        let diff  = Set.fromList tags Set.\\ Set.fromList ptags,
        not (Set.null diff) -> do
          liftTCM $ reportSDoc "tc.cover.precomputed" 10 $ vcat
            [ hsep $ "ptags =" : map prettyTCM ptags
            , hsep $ "tags  =" : map prettyTCM tags
            ]
          throwError (GenericSplitError "precomputed set of constructors does not cover all cases")

    _  -> do
      liftTCM $ checkSortOfSplitVar dr $ unDom t
      return $ Right $ Covering (lookupPatternVar sc x) ns

  where
    relTarget = caseMaybe target Relevant $ \b ->
            if isProp (unArg b)
            then Irrelevant
            else getRelevance b

    inContextOfT, inContextOfDelta2 :: (MonadTCM tcm, MonadDebug tcm) => tcm a -> tcm a
    inContextOfT      = addContext tel . escapeContext (x + 1)
    inContextOfDelta2 = addContext tel . escapeContext x

    -- Debug printing
    debugInit tel x ps cps = liftTCM $ inTopContext $ do
      reportSDoc "tc.cover.top" 10 $ vcat
        [ "TypeChecking.Coverage.split': split"
        , nest 2 $ vcat
          [ "tel     =" <+> prettyTCM tel
          , "x       =" <+> prettyTCM x
          , "ps      =" <+> do addContext tel $ prettyTCMPatternList $ fromSplitPatterns ps
          , "cps     =" <+> prettyTCM cps
          ]
        ]

    debugHoleAndType delta1 delta2 s ps t =
      liftTCM $ reportSDoc "tc.cover.top" 10 $ nest 2 $ vcat $
        [ "p      =" <+> text (patVarNameToString s)
        , "ps     =" <+> text (show ps)
        , "delta1 =" <+> prettyTCM delta1
        , "delta2 =" <+> inContextOfDelta2 (prettyTCM delta2)
        , "t      =" <+> inContextOfT (prettyTCM t)
        ]

-- | What could go wrong if we try to split on the result?
data CosplitError
  = CosplitNoTarget
      -- ^ We do not know the target type of the clause.
  | CosplitNoRecordType Telescope Type
      -- ^ Type living in the given telescope is not a record type.
  -- Andreas, 2018-06-09, issue #2170: splitting with irrelevant fields is always fine!
  -- -- | CosplitIrrelevantProjections
  -- --     -- ^ Record has irrelevant fields, but we do not have irrelevant projections.

instance PrettyTCM CosplitError where
  prettyTCM = \case
    CosplitNoTarget ->
      "target type is unknown"
    -- Andreas, 2018-06-09, issue #2170: splitting with irrelevant fields is always fine!
    -- CosplitIrrelevantProjections ->
    --   "record has irrelevant fields, but no corresponding projections"
    CosplitNoRecordType tel t -> addContext tel $ do
      "target type " <+> prettyTCM t <+> " is not a record type"

-- | @splitResult f sc = return res@
--
--   If the target type of @sc@ is a record type, a covering set of
--   split clauses is returned (@sc@ extended by all valid projection patterns),
--   otherwise @res == Nothing@.
--   Note that the empty set of split clauses is returned if the record has no fields.
splitResult :: QName -> SplitClause -> TCM (Either CosplitError Covering)
splitResult f sc@(SClause tel ps _ _ target) = do
  reportSDoc "tc.cover.split" 10 $ vcat
    [ "splitting result:"
    , nest 2 $ "f      =" <+> prettyTCM f
    , nest 2 $ "target =" <+> (addContext tel $ maybe empty prettyTCM target)
    ]
  -- if we want to split projections, but have no target type, we give up
  let failure = return . Left
  caseMaybe target (failure CosplitNoTarget) $ \ t -> do
    isR <- addContext tel $ isRecordType $ unArg t
    case isR of
      Just (_r, vs, Record{ recFields = fs }) -> do
        reportSDoc "tc.cover" 20 $ sep
          [ text $ "we are of record type _r = " ++ prettyShow _r
          , text   "applied to parameters vs = " <+> (addContext tel $ prettyTCM vs)
          , text $ "and have fields       fs = " ++ prettyShow fs
          ]
        -- Andreas, 2018-06-09, issue #2170, we always have irrelevant projections
        -- available on the lhs.
        -- -- Andreas, 2018-03-19, issue #2971, check that we have a "strong" record type,
        -- -- i.e., with all the projections.  Otherwise, we may not split.
        -- ifNotM (strongRecord fs) (failure CosplitIrrelevantProjections) $ {-else-} do
        let es = patternsToElims $ fromSplitPatterns ps
        -- Note: module parameters are part of ps
        let self  = defaultArg $ Def f [] `applyE` es
            pargs = vs ++ [self]
        reportSDoc "tc.cover" 20 $ sep
          [ text   "we are              self = " <+> (addContext tel $ prettyTCM $ unArg self)
          ]
        let n = defaultArg $ permRange $ fromMaybe __IMPOSSIBLE__ $ dbPatPerm $ fromSplitPatterns ps
            -- Andreas & James, 2013-11-19 includes the dot patterns!
            -- See test/succeed/CopatternsAndDotPatterns.agda for a case with dot patterns
            -- and copatterns which fails for @n = size tel@ with a broken case tree.

        -- Andreas, 2016-07-22 read the style of projections from the user's lips
        projOrigin <- ifM (optPostfixProjections <$> pragmaOptions) (return ProjPostfix) (return ProjPrefix)
        Right . Covering n <$> do
          forM fs $ \ proj -> do
            -- compute the new target
            dType <- defType <$> do getConstInfo $ unArg proj -- WRONG: typeOfConst $ unArg proj
            let -- type of projection instantiated at self
                target' = Just $ proj $> dType `piApply` pargs      -- Always visible (#2287)
                projArg = fmap (Named Nothing . ProjP projOrigin) $ setHiding NotHidden proj
                sc' = sc { scPats   = scPats sc ++ [projArg]
                         , scSubst  = idS
                         , scTarget = target'
                         }
            return (SplitCon (unArg proj), sc')
      _ -> failure $ CosplitNoRecordType tel $ unArg t
  -- Andreas, 2018-06-09, issue #2170: splitting with irrelevant fields is always fine!
  -- where
  -- -- A record type is strong if it has all the projections.
  -- -- This is the case if --irrelevant-projections or no field is irrelevant.
  -- -- TODO: what about shape irrelevance?
  -- strongRecord :: [Arg QName] -> TCM Bool
  -- strongRecord fs = (optIrrelevantProjections <$> pragmaOptions) `or2M`
  --   (return $ not $ any isIrrelevant fs)


-- * Boring instances

-- | For debugging only.
instance PrettyTCM SplitClause where
  prettyTCM (SClause tel pats sigma cps target) = sep
    [ "SplitClause"
    , nest 2 $ vcat
      [ "tel          =" <+> prettyTCM tel
      , "pats         =" <+> sep (map (prettyTCM . namedArg) pats)
      , "subst        =" <+> (text . show) sigma
      , "checkpoints  =" <+> prettyTCM cps
      , "target       =" <+> do
          caseMaybe target empty $ \ t -> do
            addContext tel $ prettyTCM t
      -- Triggers crash (see Issue 1374).
      -- , "subst target = " <+> do
      --     caseMaybe target empty $ \ t -> do
      --       addContext tel $ prettyTCM $ applySubst sigma t
      ]
    ]
