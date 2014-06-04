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

import           Control.Applicative              (Applicative(pure, (<*>)))
import           Data.Void                        (Void)
import qualified Data.Map.Strict                  as Map
import qualified Data.Set                         as Set
import           Data.Typeable                    (Typeable)
import           Data.Maybe                       (fromMaybe)
import           Control.Monad                    (ap)

import           Syntax.Abstract                  (SrcLoc, noSrcLoc, HasSrcLoc, srcLoc)
import           Syntax.Abstract.Pretty           ()
import qualified Types.Context                    as Ctx
import qualified Types.Signature                  as Sig
import           Types.Var

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

runTC :: ClosedTC t a -> IO (Either TCErr (a, TCState t))
runTC (TC m) = return $ case m (initEnv, initState) of
  OK ts x   -> Right (x, ts)
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

-- -- Problem handling
-- ------------------------------------------------------------------------

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
    :: (Typeable a, Typeable v)
    => Set.Set MetaVar -> StuckTC t v a -> TC t v (ProblemId t v a)
newProblem mvs m = do
    ctx <- askContext
    let prob = Problem ctx (\() -> m)
    pid <- addNewProblem prob
    modify_ $ \ts ->
      let metaVarProbs = Set.foldr' (\mv -> insertInMapOfSets mv pid)
                                    (tsMetaVarProblems ts) mvs
      in ts{tsMetaVarProblems = metaVarProbs}
    return $ ProblemId pid

bindProblem
    :: (Typeable a, Typeable b, Typeable v)
    => ProblemId t v a -> (a -> StuckTC t v b) -> TC t v (ProblemId t v b)
bindProblem (ProblemId pid0) f = do
    ctx <- askContext
    let prob = Problem ctx f
    pid <- addNewProblem prob
    modify_ $ \ts ->
      ts{tsBoundProblems = insertInMapOfSets pid0 pid (tsBoundProblems ts)}
    return $ ProblemId pid

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
