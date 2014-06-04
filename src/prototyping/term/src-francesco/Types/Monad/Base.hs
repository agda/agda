module Types.Monad.Base
    ( -- * Monad definition
      TC
    , ClosedTC
    , TCState
    , TCErr(..)
    , initTCState
    , runTC
      -- * Errors
    , typeError
      -- * Source location
    , atSrcLoc
      -- * Signature
    , getSignature
    , putSignature
      -- * Context
    , askContext
    , localContext
      -- * Problem handling
    , ProblemId
    , Stuck(..)
    , StuckTC
    , newProblem
    , bindProblem
    , waitOnProblem
    , solveNextProblem
    ) where

import Prelude                                    hiding (abs, pi)

import           Control.Monad.State              (State, runState)
import qualified Control.Monad.State              as State
import           Control.Applicative              (Applicative(pure, (<*>)))
import           Data.Void                        (Void)
import qualified Data.Map.Strict                  as Map
import qualified Data.Set                         as Set
import           Data.Typeable                    (Typeable, cast)
import           Data.Maybe                       (fromMaybe)
import           Control.Monad                    (ap, void, msum)
import           Data.Functor                     ((<$>))

import           Syntax.Abstract                  (SrcLoc, noSrcLoc, HasSrcLoc, srcLoc)
import           Syntax.Abstract.Pretty           ()
import qualified Types.Context                    as Ctx
import qualified Types.Signature                  as Sig
import           Types.Var
import           Types.Term

import           Debug.Trace                      (trace)

-- Monad definition
------------------------------------------------------------------------

newtype TC t v a = TC {unTC :: (TCEnv t v, TCState t) -> TCRes t a}
  deriving (Functor)

data TCRes t a
  = OK (TCState t) a
  | Error TCErr
  deriving (Functor)

instance Applicative (TC t v) where
  pure  = return
  (<*>) = ap

instance Monad (TC t v) where
  return x = TC $ \(_, ts) -> OK ts x

  TC m >>= f =
    TC $ \s@(te, _) -> case m s of
      OK ts x   -> unTC (f x) (te, ts)
      Error err -> Error err

type ClosedTC t = TC t Void

runTC :: TCState t -> ClosedTC t a -> IO (Either TCErr (a, TCState t))
runTC ts (TC m) = return $ case m (initEnv, ts) of
  OK ts' x  -> Right (x, ts')
  Error err -> Left err

local :: (TCEnv t v -> TCEnv t v') -> TC t v' a -> TC t v a
local f (TC m) = TC $ \(te, ts) -> m (f te, ts)

modify :: (TCState t -> (TCState t, a)) -> TC t v a
modify f = TC $ \(_, ts) -> let (ts', x) = f ts in OK ts' x

modify_ :: (TCState t -> TCState t) -> TC t v ()
modify_ f = modify $ \ts -> (f ts, ())

data TCEnv t v = TCEnv
    { teContext       :: !(Ctx.ClosedCtx t v)
    , teCurrentSrcLoc :: !SrcLoc
    }

initEnv :: Closed (TCEnv t)
initEnv = TCEnv
  { teContext       = Ctx.Empty
  , teCurrentSrcLoc = noSrcLoc
  }

data TCState t = TCState
    { tsSignature        :: !(Sig.Signature t)
    , tsProblems         :: !(Map.Map ProblemIdInt (Problem t))
    , tsSolvedProblems   :: !(Map.Map ProblemIdInt SolvedProblem)
    , tsMetaVarProblems  :: !(Map.Map MetaVar (Set.Set ProblemIdInt))
    -- ^ Problems waiting on a metavariable.  Note that a problem might
    -- appear as a dependency of multiple metavariables.
    , tsBoundProblems    :: !(Map.Map ProblemIdInt (Set.Set ProblemIdInt))
    -- ^ Problems bound to another problem.
    , tsWaitingProblems  :: !(Map.Map ProblemIdInt (Set.Set ProblemIdInt))
    -- ^ Problems waiting on another problem.
    }

initTCState :: TCState t
initTCState = TCState
  { tsSignature        = Sig.empty
  , tsProblems         = Map.empty
  , tsSolvedProblems   = Map.empty
  , tsMetaVarProblems  = Map.empty
  , tsBoundProblems    = Map.empty
  , tsWaitingProblems  = Map.empty
  }

data TCErr
    = StrErr SrcLoc String

instance Show TCErr where
  show (StrErr p s) =
    "Error at " ++ show p ++ ":\n" ++ unlines (map ("  " ++) (lines s))

-- Errors
------------------------------------------------------------------------

typeError :: String -> TC t v b
typeError err = TC $ \(te, _) -> Error $ StrErr (teCurrentSrcLoc te) err

-- SrcLoc
------------------------------------------------------------------------

atSrcLoc :: HasSrcLoc a => a -> TC t v b -> TC t v b
atSrcLoc x = local $ \te -> te{teCurrentSrcLoc = srcLoc x}

-- Signature
------------------------------------------------------------------------

getSignature :: TC t v (Sig.Signature t)
getSignature = modify $ \ts -> (ts, tsSignature ts)

putSignature :: Sig.Signature t -> TC t v ()
putSignature sig = modify_ $ \ts -> ts{tsSignature = sig}

-- Context
------------------------------------------------------------------------

askContext :: TC t v (Ctx.ClosedCtx t v)
askContext = TC $ \(te, ts) -> OK ts $ teContext te

localContext
    :: (Ctx.ClosedCtx t v -> Ctx.ClosedCtx t v') -> TC t v' a -> TC t v a
localContext f = local $ \env -> env{teContext = f (teContext env)}

-- Problem handling
------------------------------------------------------------------------

type ProblemIdInt = Int

newtype ProblemId (t :: * -> *) v a = ProblemId ProblemIdInt

data Problem t =
    forall a b v. (Typeable a, Typeable b, Typeable v) =>
    Problem !(Ctx.ClosedCtx t v) !(a -> StuckTC t v b)

data SolvedProblem = forall a. Typeable a => SolvedProblem !a

data Stuck t v a
    = StuckOn (ProblemId t v a)
    | NotStuck a

type StuckTC t v a = TC t v (Stuck t v a)

addNewProblem :: Problem t -> TC t v ProblemIdInt
addNewProblem prob = modify $ \ts ->
    let probs = tsProblems ts
        pid = case Map.maxViewWithKey probs of
                Nothing             -> 0
                Just ((pid0, _), _) -> pid0 + 1
    in (ts{tsProblems = Map.insert pid prob probs}, pid)

insertInMapOfSets
    :: (Ord k, Ord v) => k -> v -> Map.Map k (Set.Set v) -> Map.Map k (Set.Set v)
insertInMapOfSets k v m =
    Map.insert k (Set.insert v (fromMaybe Set.empty (Map.lookup k m))) m

newProblem
    :: (Typeable a, Typeable v, Typeable t)
    => Set.Set MetaVar -> (Closed (Term t) -> StuckTC t v a) -> TC t v (ProblemId t v a)
newProblem mvs m = do
    ctx <- askContext
    let prob = Problem ctx m
    pid <- addNewProblem prob
    modify_ $ \ts ->
      let metaVarProbs = Set.foldr' (\mv -> insertInMapOfSets mv pid)
                                    (tsMetaVarProblems ts) mvs
      in ts{tsMetaVarProblems = metaVarProbs}
    return $ ProblemId pid

bindProblem'
    :: (Typeable a, Typeable b, Typeable v)
    => (Problem t -> TC t v ProblemIdInt)
    -> ProblemId t v a -> (a -> StuckTC t v b) -> TC t v (ProblemId t v b)
bindProblem' addProblem (ProblemId pid0) f = do
    ctx <- askContext
    let prob = Problem ctx f
    pid <- addProblem prob
    modify_ $ \ts ->
      ts{tsBoundProblems = insertInMapOfSets pid0 pid (tsBoundProblems ts)}
    return $ ProblemId pid

bindProblem
    :: (Typeable a, Typeable b, Typeable v)
    => ProblemId t v a -> (a -> StuckTC t v b) -> TC t v (ProblemId t v b)
bindProblem = bindProblem' addNewProblem

waitOnProblem
    :: (Typeable a, Typeable b, Typeable v')
    => ProblemId t v a -> StuckTC t v' b -> TC t v' (ProblemId t v' b)
waitOnProblem (ProblemId pid0) m = do
    ctx <- askContext
    let prob = Problem ctx (\() -> m)
    pid <- addNewProblem prob
    modify_ $ \ts ->
      ts{tsBoundProblems = insertInMapOfSets pid0 pid (tsBoundProblems ts)}
    return $ ProblemId pid

reAddProblem :: ProblemIdInt -> Problem t -> TC t v ProblemIdInt
reAddProblem pid prob = modify $ \ts ->
    let probs = tsProblems ts
    in (ts{tsProblems = Map.insert pid prob probs}, pid)

solveNextProblem
  :: forall t. (Typeable t)
  => TCState t -> IO (Maybe (Either TCErr (TCState t)))
solveNextProblem ts0 = case run of
    Nothing       -> return Nothing
    Just (ts', m) -> (Just . fmap snd) <$> runTC ts' m
  where
    -- We cleanup stale problems in the 'MetaVar's dependencies lazily.
    checkMetaVars
      :: [MetaVar]
      -> State (TCState t) [(MetaVar, ProblemIdInt)]
    checkMetaVars [] =
      return []
    checkMetaVars (mv : mvs) = do
      Just mvProbs <- return $ Map.lookup mv (tsMetaVarProblems ts0)
      -- TODO Avoid rebuilding the whole thing if there aren't changes
      let mvProbs' = Set.filter (`Map.member` tsProblems ts0) mvProbs
      State.modify $ \ts' ->
        ts'{tsMetaVarProblems = Map.insert mv mvProbs' (tsMetaVarProblems ts')}
      (map (mv ,) (Set.toList mvProbs') ++) <$> checkMetaVars mvs

    metaVarsProblems :: [(MetaVar, ProblemIdInt)]
    (metaVarsProblems, ts) =
      flip runState ts0 $ checkMetaVars $ Set.toList $
      Set.intersection (Sig.instantiatedMetaVars (tsSignature ts0))
                       (Map.keysSet (tsMetaVarProblems ts0))

    boundProblems :: [(ProblemIdInt, ProblemIdInt)]
    boundProblems =
      let solvedBoundOn = Set.intersection (Map.keysSet (tsSolvedProblems ts))
                                           (Map.keysSet (tsBoundProblems ts))
      in concat [ let Just probs = Map.lookup boundOn (tsBoundProblems ts)
                  in map (boundOn,) (Set.toList probs)
                | boundOn <- Set.toList solvedBoundOn
                ]

    waitingProblems :: [(ProblemIdInt, ProblemIdInt)]
    waitingProblems =
      let solvedWaitingOn = Set.intersection (Map.keysSet (tsSolvedProblems ts))
                                             (Map.keysSet (tsWaitingProblems ts))
      in concat [ let Just probs = Map.lookup waitingOn (tsWaitingProblems ts)
                  in map (waitingOn, ) (Set.toList probs)
                | waitingOn <- Set.toList solvedWaitingOn
                ]

    probToRun :: Maybe (SolvedProblem, ProblemIdInt, Problem t, TCState t)
    probToRun = msum
      [ do ((boundOn, pid) : _) <- return boundProblems
           let Just solved = Map.lookup boundOn (tsSolvedProblems ts)
           prob <- Map.lookup pid (tsProblems ts)
           let Just probs  = Map.lookup boundOn (tsBoundProblems ts)
           return
             ( solved
             , pid
             , prob
             , ts{tsBoundProblems = Map.insert pid (Set.delete pid probs) (tsBoundProblems ts)}
             )
      , do ((waitingOn, pid) : _) <- return waitingProblems
           let Just prob   = Map.lookup pid (tsProblems ts)
           let Just probs  = Map.lookup waitingOn (tsWaitingProblems ts)
           return
             ( SolvedProblem ()
             , pid
             , prob
             , ts{tsWaitingProblems = Map.insert pid (Set.delete pid probs) (tsWaitingProblems ts)}
             )
      , do ((mv, pid) : _) <- return metaVarsProblems
           let Just body = Sig.getMetaVarBody (tsSignature ts) mv
           let Just prob = Map.lookup pid (tsProblems ts)
           let Just mvProbs = Map.lookup mv (tsMetaVarProblems ts)
           return
             ( SolvedProblem body
             , pid
             , prob
             , ts{tsMetaVarProblems = Map.insert mv (Set.delete pid mvProbs) (tsMetaVarProblems ts)}
             )
      ]

    run :: Maybe (TCState t, ClosedTC t ())
    run = do
      (SolvedProblem x, pid, Problem ctx m, ts') <- probToRun
      trace ("Solving problem " ++ show pid) $ return ()
      trace ("Remaining problems " ++ show (Map.size (tsProblems ts'))) $ return ()
      let n x' = do
            stuck <- m x'
            case stuck of
              NotStuck y ->
                -- Mark the problem as solved.
                modify_ $ \ts'' ->
                  ts''{ tsSolvedProblems = Map.insert pid (SolvedProblem y) (tsSolvedProblems ts'')
                      , tsProblems       = Map.delete pid (tsProblems ts'')
                      }
              StuckOn pid' ->
                -- If the problem is stuck, re-add it as a dependency of
                -- what it is stuck on.
                void $ bindProblem' (reAddProblem pid) pid' $ return . NotStuck
      return $ case cast x of
        Nothing ->
          error "impossible.solveNextProblem: can't cast problem argument"
        Just x' ->
          (ts', local (\te -> te{teContext = ctx}) (n x'))
