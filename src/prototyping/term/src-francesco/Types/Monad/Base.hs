{-# LANGUAGE OverloadedStrings #-}
module Types.Monad.Base
    ( -- * Monad definition
      TC
    , ClosedTC
    , TCState
    , TCErr(..)
    , initTCState
    , runTC
      -- * Report
    , TCReport(..)
    , tcReport
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
    , ProblemIdInt
    , ProblemState
    , ProblemDescription
    , Stuck(..)
    , StuckTC
    , newProblem
    , bindProblem
    , waitOnProblem
    , solveProblems
    ) where

import Prelude                                    hiding (abs, pi)

import           Control.Applicative              (Applicative(pure, (<*>)))
import           Data.Void                        (Void)
import qualified Data.Map.Strict                  as Map
import qualified Data.Set                         as Set
import           Data.Typeable                    (Typeable)
import           Data.Dynamic                     (Dynamic, toDyn, fromDynamic)
import           Control.Monad                    (ap, void, msum, when, forM)
import           Data.Functor                     ((<$>), (<$))
import           Bound

import qualified Text.PrettyPrint.Extended        as PP
import           Text.PrettyPrint.Extended        ((<+>))
import           Syntax.Abstract                  (SrcLoc, noSrcLoc, HasSrcLoc, srcLoc)
import           Syntax.Abstract.Pretty           ()
import qualified Types.Context                    as Ctx
import qualified Types.Signature                  as Sig
import           Types.Term
import           Eval

-- Monad definition
------------------------------------------------------------------------

-- | The "type checking" monad.
--
-- It carries around a signature, that we can modify
-- ('modifySignature'), and a context with the current scope, which we
-- can inspect and locally modify ('askContext', 'localContext').  It
-- also lets you track of the current location in the source code.
--
-- Moreover, it lets us suspend computations waiting on a 'MetaVar' to
-- be instantiated, or on another suspended computation to be completed.
-- See 'ProblemId' and related functions.
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

-- | Takes a 'TCState' and a computation on a closed context and
-- produces an error or a result with a new state.
runTC :: TCState t -> ClosedTC t a -> IO (Either TCErr (a, TCState t))
runTC ts (TC m) = return $ case m (initEnv, ts) of
  OK ts' x  -> Right (x, ts')
  Error err -> Left err

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
    , tsUnsolvedProblems :: !(Map.Map ProblemIdInt (Problem t))
    , tsSolvedProblems   :: !(Map.Map ProblemIdInt ProblemSolution)
    }

-- | An empty state.
initTCState :: TCState t
initTCState = TCState
  { tsSignature        = Sig.empty
  , tsUnsolvedProblems = Map.empty
  , tsSolvedProblems   = Map.empty
  }

data TCErr
    = StrErr SrcLoc String

instance Show TCErr where
  show (StrErr p s) =
    "Error at " ++ show p ++ ":\n" ++ unlines (map ("  " ++) (lines s))

-- TCReport
------------------------------------------------------------------------

-- | A type useful to inspect what's going on.
data TCReport t = TCReport
  { trSignature        :: !(Sig.Signature t)
  , trSolvedProblems   :: !(Set.Set ProblemIdInt)
  , trUnsolvedProblems :: !(Map.Map ProblemIdInt (ProblemState, PP.Doc))
    -- ^ The unsolved problems, along with their state and a
    -- description.
  }

tcReport :: (IsTerm t) => TCState t -> TCReport t
tcReport ts = TCReport
  { trSignature        = sig
  , trSolvedProblems   = Map.keysSet $ tsSolvedProblems ts
  , trUnsolvedProblems = fmap (\p@(Problem _ _ _ desc) -> (pState p, PP.pretty (nf' sig desc))) $
                         tsUnsolvedProblems ts
  }
  where
    sig = tsSignature ts

-- Errors
------------------------------------------------------------------------

-- | Fail with an error message.
typeError :: String -> TC t v b
typeError err = TC $ \(te, _) -> Error $ StrErr (teCurrentSrcLoc te) err

-- SrcLoc
------------------------------------------------------------------------

-- | Run some action with the given 'SrcLoc'.
atSrcLoc :: HasSrcLoc a => a -> TC t v b -> TC t v b
atSrcLoc x = local $ \te -> te{teCurrentSrcLoc = srcLoc x}

-- Signature
------------------------------------------------------------------------

-- Basics
---------

-- | Gets the signature.
getSignature :: TC t v (Sig.Signature t)
getSignature = modify $ \ts -> (ts, tsSignature ts)

-- | Puts a new signature.
putSignature :: Sig.Signature t -> TC t v ()
putSignature sig = modify_ $ \ts -> ts{tsSignature = sig}

-- Context
------------------------------------------------------------------------

-- | Asks the current context.
askContext :: TC t v (Ctx.ClosedCtx t v)
askContext = TC $ \(te, ts) -> OK ts $ teContext te

-- | Runs an action with a modified context.
localContext
    :: (Ctx.ClosedCtx t v -> Ctx.ClosedCtx t v') -> TC t v' a -> TC t v a
localContext f = local $ \env -> env{teContext = f (teContext env)}

-- Problem handling
------------------------------------------------------------------------

-- | An 'Int' version of the 'ProblemId', useful for debugging (see
-- 'TCReport').
type ProblemIdInt = Int

-- | A 'ProblemId' identifies a suspended computation and carries around
-- the type of the result of the computation it refers to.
newtype ProblemId (t :: * -> *) v a = ProblemId ProblemIdInt
  deriving (Show)

-- | To store problems, we store the context of the suspended
-- computation; and its state and description living in said context.
--
-- Both the type of the bound variable and the result type are
-- 'Typeable' since we store the solutions and problems dynamically so
-- that they can all be in the same 'Map.Map'.
data Problem t = forall a b v p. (Typeable a, Typeable b, IsVar v, Nf p, PP.Pretty (p t v)) => Problem
    { pContext     :: !(Ctx.ClosedCtx t v)
    , pProblem     :: !(a -> StuckTC t v b)
    , pState       :: !ProblemState
    , pDescription :: !(p t v)
    }

data ProblemState
    = BoundToMetaVars  !(Set.Set MetaVar)
    | WaitingOnProblem !ProblemIdInt
    | BoundToProblem   !ProblemIdInt
    deriving (Show)

instance PP.Pretty ProblemState where
  pretty (BoundToMetaVars mvs)  = "BoundToMetaVars" <+> PP.pretty (Set.toList mvs)
  pretty (WaitingOnProblem pid) = "WaitingOnProblem" <+> PP.pretty pid
  pretty (BoundToProblem pid)   = "BoundToProblem" <+> PP.pretty pid

-- | As remarked, we store the problems solutions dynamically to have
-- them in a single 'Map.Map'.
newtype ProblemSolution = ProblemSolution Dynamic

problemSolution :: Typeable a => a -> ProblemSolution
problemSolution = ProblemSolution . toDyn

-- | Datatype useful to represent computations that might return a
-- result directly or the 'ProblemId' of a problem containing the
-- result.
data Stuck t v a
    = StuckOn (ProblemId t v a)
    | NotStuck a

type StuckTC t v a = TC t v (Stuck t v a)

saveSrcLoc :: Problem t -> TC t v (Problem t)
saveSrcLoc (Problem ctx m st desc) = do
  loc <- TC $ \(te, ts) -> OK ts $ teCurrentSrcLoc te
  return $ Problem ctx (\x -> atSrcLoc loc (m x)) st desc

addProblem :: ProblemIdInt -> Problem t -> TC t v (ProblemId t v a)
addProblem pid prob = do
  modify $ \ts -> (ts{tsUnsolvedProblems = Map.insert pid prob (tsUnsolvedProblems ts)}, ProblemId pid)

addFreshProblem :: Problem t -> TC t v (ProblemId t v a)
addFreshProblem prob = do
  ts <- get
  let probs = tsUnsolvedProblems ts
  let pid = case Map.maxViewWithKey probs of
              Nothing             -> 0
              Just ((pid0, _), _) -> pid0 + 1
  addProblem pid prob

-- | Problem description.  We have a 'Nf' constraint on it so that when
-- printing the description out later we can normalize terms with the
-- new signature.
type ProblemDescription p (t :: * -> *) v = p t v

-- | Store a new problem dependend on a set of 'MetaVar's.  When one of
-- them will be instantiated, the computation can be executed again.
newProblem
    :: (Typeable a, IsVar v, IsTerm t, Nf p, PP.Pretty (p t v))
    => Set.Set MetaVar
    -> ProblemDescription p t v
    -> StuckTC t v a
    -> TC t v (ProblemId t v a)
newProblem mvs _ _ | Set.null mvs = do
    error "Types.Monad.Base.newProblem: empty set of metas."
newProblem mvs desc m = do
    ctx <- askContext
    prob <- saveSrcLoc $ Problem
      { pContext     = ctx
      , pProblem     = \() -> m
      , pState       = BoundToMetaVars mvs
      , pDescription = desc
      }
    addFreshProblem prob

-- | @bindProblem pid desc (\x -> m)@ binds computation @m@ to problem
-- @pid@. When @pid@ is solved with result @t@, @m t@ will be executed.
bindProblem
    :: (Typeable a, Typeable b, IsTerm t, IsVar v, Nf p, PP.Pretty (p t v))
    => ProblemId t v a
    -> ProblemDescription p t v
    -> (a -> StuckTC t v b)
    -> TC t v (ProblemId t v b)
bindProblem (ProblemId pid) desc f = do
    ctx <- askContext
    prob <- saveSrcLoc $ Problem
      { pContext     = ctx
      , pProblem     = f
      , pState       = BoundToProblem pid
      , pDescription = desc
      }
    addFreshProblem prob

-- | @waitOnProblem pid desc m@ waits until @pid@ is solved before
-- executing @m@.  The difference between 'waitOnProblem' and
-- 'bindProblem' is that with 'waitOnProblem' @m@ does not need to be in
-- the same context as @pid@, as reflected in the types of the
-- variables.
waitOnProblem
    :: (Typeable a, Typeable b, IsTerm t, IsVar v', Nf p, PP.Pretty (p t v'))
    => ProblemId t v a
    -> ProblemDescription p t v'
    -> StuckTC t v' b
    -> TC t v' (ProblemId t v' b)
waitOnProblem (ProblemId pid) desc m = do
    ctx <- askContext
    prob <- saveSrcLoc $ Problem
      { pContext     = ctx
      , pProblem     = \() -> m
      , pState       = WaitingOnProblem pid
      , pDescription = desc
      }
    addFreshProblem prob

-- | Description for problems that after execution are stuck on another
-- problem -- we preserve the original description and we add the
-- "stuckness".
data StuckProblemDescription p (t :: * -> *) v =
  StuckProblemDescription ProblemIdInt (ProblemDescription p t v)

instance (Bound p) => Bound (StuckProblemDescription p) where
  StuckProblemDescription pid t >>>= f = StuckProblemDescription pid (t >>>= f)

instance (Nf p) => Nf (StuckProblemDescription p) where
  nf' sig (StuckProblemDescription pid t) = StuckProblemDescription pid (nf' sig t)

instance (IsVar v, IsTerm t, PP.Pretty (p t v)) => PP.Pretty (StuckProblemDescription p t v) where
  pretty (StuckProblemDescription pid desc) =
    ("Stuck on" PP.<+> PP.pretty pid) PP.$$ PP.nest 2 (PP.pretty desc)

-- | This computation solves all problems that are solvable in the
-- current state.  Returns whether any problem was solved.
solveProblems :: (IsTerm t) => ClosedTC t Bool
solveProblems = do
  unsolvedProbs <- Map.toList . tsUnsolvedProblems <$> get
  -- Go over all unsolved problems and record if we made progress in any
  -- of them.
  progress <- fmap or $ forM unsolvedProbs $ \(pid, (Problem ctx prob state desc)) -> do
    -- Collect the state necessary to execute the current problem, if
    -- available.
    mbSolution :: Maybe ProblemSolution <- case state of
      -- If we're waiting on metavars, check if at least one is
      -- instantiated.  The state will be ().
      BoundToMetaVars mvs -> do
        sig <- getSignature
        return $ msum
          [ problemSolution () <$ Map.lookup mv (Sig.metaVarsBodies sig)
          | mv <- Set.toList mvs
          ]
      -- If we're bound to another problem, retrieve its result if
      -- available.
      BoundToProblem boundTo -> do
        Map.lookup boundTo . tsSolvedProblems <$> get
      -- If we're just waiting on it, do the same but return ().
      WaitingOnProblem waitingOn -> do
        (problemSolution () <$) . Map.lookup waitingOn . tsSolvedProblems <$> get
    case mbSolution of
      Nothing       -> return False
      Just solution -> True <$ solveProblem pid desc ctx prob solution
  progress <$ when progress (void solveProblems)
  where
    solveProblem
      :: (Typeable a, Typeable b, IsTerm t, IsVar v, Nf p, PP.Pretty (p t v))
      => ProblemIdInt
      -- ^ pid of the problem we're solving.
      -> ProblemDescription p t v
      -- ^ ...and its description.
      -> Ctx.ClosedCtx t v
      -- ^ ...and its context
      -> (a -> StuckTC t v b)
      -- ^ ...and the suspended computation
      -> ProblemSolution
      -- ^ Solution to the problem we were waiting on.
      -> ClosedTC t ()
    solveProblem pid desc ctx m (ProblemSolution x) = do
      -- From how the functions adding problems are designed we know
      -- that the types will match up.
      Just x' <- return $ fromDynamic x
      -- Delete the problem wrom the list of unsolved problems.
      modify_ $ \ts -> ts{tsUnsolvedProblems = Map.delete pid (tsUnsolvedProblems ts)}
      localContext (\_ -> ctx) $ do
        -- Execute the suspended computation
        stuck <- m x'
        case stuck of
          NotStuck y -> do
            -- Mark the problem as solved.
            modify_ $ \ts ->
              ts{tsSolvedProblems = Map.insert pid (problemSolution y) (tsSolvedProblems ts)}
          StuckOn (ProblemId boundTo) -> do
            -- If the problem is stuck, re-add it as a dependency of
            -- what it is stuck on.
            void $ addProblem pid $ Problem ctx m (BoundToProblem boundTo) $
              StuckProblemDescription boundTo desc

-- Utils
------------------------------------------------------------------------

local :: (TCEnv t v -> TCEnv t v') -> TC t v' a -> TC t v a
local f (TC m) = TC $ \(te, ts) -> m (f te, ts)

modify :: (TCState t -> (TCState t, a)) -> TC t v a
modify f = TC $ \(_, ts) -> let (ts', x) = f ts in OK ts' x

modify_ :: (TCState t -> TCState t) -> TC t v ()
modify_ f = modify $ \ts -> (f ts, ())

get :: TC t v (TCState t)
get = modify $ \ts -> (ts, ts)
