module Types.Monad.Base
    ( -- * Monad definition
      TC
    , ClosedTC
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
    ) where

import Prelude                                    hiding (abs, pi)

import           Control.Monad.State              (gets, modify)
import           Control.Applicative              (Applicative)
import           Control.Monad.Trans.State        (State, evalState)
import           Control.Monad.Trans.Reader       (asks, local, ReaderT(ReaderT), runReaderT)
import           Control.Monad.Trans.Error        (throwError, Error, strMsg, ErrorT, runErrorT)
import           Data.Void                        (Void)
import           Control.Monad.Trans.Class        (lift)
import qualified Data.Map.Strict                  as Map
import qualified Data.Set                         as Set
import           Data.Typeable                    (Typeable)
import           Data.Maybe                       (fromMaybe)

import           Syntax.Abstract                  (SrcLoc, noSrcLoc, HasSrcLoc, srcLoc)
import           Syntax.Abstract.Pretty           ()
import qualified Types.Context                    as Ctx
import qualified Types.Signature                  as Sig
import           Types.Var

-- Monad definition
------------------------------------------------------------------------

newtype TC t v a =
    TC {unTC :: ReaderT (TCEnv t v) (ErrorT TCErr (State (TCState t))) a}
    deriving (Functor, Applicative, Monad)

type ClosedTC t = TC t Void

runTC :: ClosedTC t a -> IO (Either TCErr a)
runTC m = return $ flip evalState initState
                 $ runErrorT
                 $ flip runReaderT initEnv
                 $ unTC m

tcLocal :: (TCEnv t v -> TCEnv t v') -> TC t v' a -> TC t v a
tcLocal f (TC (ReaderT m)) = TC (ReaderT (m . f))

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
    { tsSignature       :: !(Sig.Signature t)
    , tsProblems        :: !(Map.Map ProblemIdInt (Problem t))
    , tsMetaVarProblems :: !(Map.Map MetaVar (Set.Set ProblemIdInt))
    -- ^ Problems waiting on a metavariable.  Note that a problem might
    -- appear as a dependency of multiple metavariables.
    , tsBoundProblems   :: !(Map.Map ProblemIdInt (Set.Set ProblemIdInt))
    -- ^ Problems bound to another problem.
    , tsWaitingProblems :: !(Map.Map ProblemIdInt (Set.Set ProblemIdInt))
    -- ^ Problems waiting on another problem.
    }

initState :: TCState t
initState = TCState
  { tsSignature       = Sig.empty
  , tsProblems        = Map.empty
  , tsMetaVarProblems = Map.empty
  , tsBoundProblems   = Map.empty
  , tsWaitingProblems = Map.empty
  }

data TCErr
    = StrErr SrcLoc String

instance Error TCErr where
  strMsg = StrErr noSrcLoc

instance Show TCErr where
  show (StrErr p s) =
    "Error at " ++ show p ++ ":\n" ++ unlines (map ("  " ++) (lines s))

-- Errors
------------------------------------------------------------------------

typeError :: String -> TC t v b
typeError err = do
  loc <- TC $ asks teCurrentSrcLoc
  TC $ lift $ throwError $ StrErr loc err

-- SrcLoc
------------------------------------------------------------------------

atSrcLoc :: HasSrcLoc a => a -> TC t v b -> TC t v b
atSrcLoc x (TC m) = TC $ local (\env -> env { teCurrentSrcLoc = srcLoc x }) m

-- Signature
------------------------------------------------------------------------

getSignature :: TC t v (Sig.Signature t)
getSignature = TC $ lift $ lift $ gets tsSignature

putSignature :: Sig.Signature t -> TC t v ()
putSignature sig = TC $ lift $ lift $ modify $ \ts -> ts{tsSignature = sig}

-- Context
------------------------------------------------------------------------

askContext :: TC t v (Ctx.ClosedCtx t v)
askContext = TC $ asks teContext

localContext
    :: (Ctx.ClosedCtx t v -> Ctx.ClosedCtx t v') -> TC t v' a -> TC t v a
localContext f = tcLocal $ \env -> env{teContext = f (teContext env)}

-- Problem handling
------------------------------------------------------------------------

type ProblemIdInt = Int

newtype ProblemId (t :: * -> *) v a = ProblemId ProblemIdInt

data Problem t =
    forall a b v. (Typeable a, Typeable b, Typeable v) =>
    Problem !(Ctx.ClosedCtx t v) !(a -> StuckTC t v b)

data Stuck t v a
    = StuckOn (ProblemId t v a)
    | NotStuck a

type StuckTC t v a = TC t v (Stuck t v a)

addNewProblem :: Problem t -> TC t v ProblemIdInt
addNewProblem prob = do
    probs <- TC $ lift $ lift $ gets tsProblems
    let pid = case Map.maxViewWithKey probs of
                Nothing             -> 0
                Just ((pid0, _), _) -> pid0 + 1
    TC $ lift $ lift $ modify $ \ts -> ts{tsProblems = Map.insert pid prob probs}
    return pid

insertInMapOfSets
    :: (Ord k, Ord v) => k -> v -> Map.Map k (Set.Set v) -> Map.Map k (Set.Set v)
insertInMapOfSets k v m =
    Map.insert k (Set.insert v (fromMaybe Set.empty (Map.lookup k m))) m

newProblem
    :: (Typeable a, Typeable v)
    => Set.Set MetaVar -> StuckTC t v a -> TC t v (ProblemId t v a)
newProblem mvs m = do
    ctx <- askContext
    let prob = Problem ctx (\() -> m)
    pid <- addNewProblem prob
    TC $ lift $ lift $ modify $ \st ->
      let metaVarProbs = Set.foldr' (\mv -> insertInMapOfSets mv pid)
                                    (tsMetaVarProblems st) mvs
      in st{tsMetaVarProblems = metaVarProbs}
    return $ ProblemId pid

bindProblem
    :: (Typeable a, Typeable b, Typeable v)
    => ProblemId t v a -> (a -> StuckTC t v b) -> TC t v (ProblemId t v b)
bindProblem (ProblemId pid0) f = do
    ctx <- askContext
    let prob = Problem ctx f
    pid <- addNewProblem prob
    TC $ lift $ lift $ modify $ \st ->
      st{tsBoundProblems = insertInMapOfSets pid0 pid (tsBoundProblems st)}
    return $ ProblemId pid

waitOnProblem
    :: (Typeable a, Typeable b, Typeable v')
    => ProblemId t v a -> StuckTC t v' b -> TC t v' (ProblemId t v' b)
waitOnProblem (ProblemId pid0) m = do
    ctx <- askContext
    let prob = Problem ctx (\() -> m)
    pid <- addNewProblem prob
    TC $ lift $ lift $ modify $ \st ->
      st{tsBoundProblems = insertInMapOfSets pid0 pid (tsBoundProblems st)}
    return $ ProblemId pid
