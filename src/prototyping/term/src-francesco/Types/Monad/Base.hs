{-# LANGUAGE OverloadedStrings #-}
module Types.Monad.Base
    ( -- * Monad definition
      TC
    , ClosedTC
    , TCState
    , TCErr(..)
    , initTCState
    , runTC
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
import           Debug.Trace                      (trace)

import qualified Text.PrettyPrint.Extended        as PP
import           Syntax.Abstract                  (SrcLoc, noSrcLoc, HasSrcLoc, srcLoc)
import           Syntax.Abstract.Pretty           ()
import qualified Types.Context                    as Ctx
import qualified Types.Signature                  as Sig
import           Types.Var
import           Types.Term

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

get :: TC t v (TCState t)
get = modify $ \ts -> (ts, ts)

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
    , tsSolvedProblems   :: !(Map.Map ProblemIdInt SolvedProblem)
    }

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

data TCReport t = TCReport
  { trSignature        :: !(Sig.Signature t)
  , trSolvedProblems   :: !Int
  , trUnsolvedProblems :: !Int
  }

tcReport :: TCState t -> TCReport t
tcReport ts = TCReport
  { trSignature        = tsSignature ts
  , trSolvedProblems   = Map.size $ tsSolvedProblems ts
  , trUnsolvedProblems = Map.size $ tsUnsolvedProblems ts
  }

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

-- Basics
---------

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
  deriving (Show)

data Problem t = forall a b v. (Typeable a, Typeable b, Typeable v) => Problem
    { pContext     :: !(Ctx.ClosedCtx t v)
    , pProblem     :: !(a -> StuckTC t v b)
    , pState       :: !ProblemState
    , pDescription :: !PP.Doc
    }

data ProblemState
    = BoundToMetaVars  !(Set.Set MetaVar)
    | WaitingOnProblem !ProblemIdInt
    | BoundToProblem   !ProblemIdInt
    deriving (Show)

newtype SolvedProblem = SolvedProblem Dynamic

solvedProblem :: Typeable a => a -> SolvedProblem
solvedProblem = SolvedProblem . toDyn

data Stuck t v a
    = StuckOn (ProblemId t v a)
    | NotStuck a

type StuckTC t v a = TC t v (Stuck t v a)

-- TODO use NFData.
forceDoc :: PP.Doc -> PP.Doc
forceDoc doc = length (PP.render doc) `seq` doc

saveSrcLoc :: Problem t -> TC t v (Problem t)
saveSrcLoc (Problem ctx m st desc) = do
  loc <- TC $ \(te, ts) -> OK ts $ teCurrentSrcLoc te
  return $ Problem ctx (\x -> atSrcLoc loc (m x)) st desc

addProblem :: Problem t -> TC t v (ProblemId t v a)
addProblem prob0 = do
  let prob = prob0{pDescription = forceDoc (pDescription prob0)}
  modify $ \ts ->
    let probs = tsUnsolvedProblems ts
        pid = case Map.maxViewWithKey probs of
                Nothing             -> 0
                Just ((pid0, _), _) -> pid0 + 1
    in (ts{tsUnsolvedProblems = Map.insert pid prob probs}, ProblemId pid)

newProblem
    :: (Typeable a, Typeable v, Typeable t, PP.Pretty p)
    => Set.Set MetaVar -> p -> (Closed (Term t) -> StuckTC t v a) -> TC t v (ProblemId t v a)
newProblem mvs description m = do
    ctx <- askContext
    prob <- saveSrcLoc $ Problem
      { pContext     = ctx
      , pProblem     = m
      , pState       = BoundToMetaVars mvs
      , pDescription = PP.pretty description
      }
    addProblem prob

bindProblem
    :: (Typeable a, Typeable b, Typeable v, PP.Pretty p)
    => ProblemId t v a -> p -> (a -> StuckTC t v b) -> TC t v (ProblemId t v b)
bindProblem (ProblemId pid) description f = do
    ctx <- askContext
    prob <- saveSrcLoc $ Problem
      { pContext     = ctx
      , pProblem     = f
      , pState       = BoundToProblem pid
      , pDescription = PP.pretty description
      }
    addProblem prob

waitOnProblem
    :: (Typeable a, Typeable b, Typeable v', PP.Pretty p)
    => ProblemId t v a -> p -> StuckTC t v' b -> TC t v' (ProblemId t v' b)
waitOnProblem (ProblemId pid) description m = do
    ctx <- askContext
    prob <- saveSrcLoc $ Problem
      { pContext     = ctx
      , pProblem     = \() -> m
      , pState       = WaitingOnProblem pid
      , pDescription = PP.pretty description
      }
    addProblem prob

-- TODO improve efficiency of this.
solveProblems :: (Typeable t) => ClosedTC t ()
solveProblems = do
  unsolvedProbs <- Map.toList . tsUnsolvedProblems <$> get
  progress <- fmap or $ forM unsolvedProbs $ \(pid, (Problem ctx prob state description)) -> do
    mbSolved <- case state of
      BoundToMetaVars mvs -> do
        sig <- getSignature
        return $ fmap solvedProblem $ msum
          [Map.lookup mv $ Sig.metaVarsBodies sig | mv <- Set.toList mvs]
      BoundToProblem boundTo -> do
        Map.lookup boundTo . tsSolvedProblems <$> get
      WaitingOnProblem waitingOn -> do
        (solvedProblem () <$) . Map.lookup waitingOn . tsSolvedProblems <$> get
    case mbSolved of
      Nothing     -> return False
      Just solved -> do trace ("SOLVING problem " ++ show pid ++ " on " ++ show state) $ return ()
                        True <$ solveProblem pid description solved ctx prob
  when progress solveProblems
  where
    solveProblem
      :: (Typeable a, Typeable b, Typeable v)
      => ProblemIdInt -> PP.Doc
      -> SolvedProblem
      -> Ctx.ClosedCtx t v -> (a -> StuckTC t v b)
      -> ClosedTC t ()
    solveProblem pid description (SolvedProblem x) ctx m = do
      Just x' <- return $ fromDynamic x
      modify_ $ \ts -> ts{tsUnsolvedProblems = Map.delete pid (tsUnsolvedProblems ts)}
      localContext (\_ -> ctx) $ do
        stuck <- m x'
        case stuck of
          NotStuck y -> do
            trace ("  SOLVED") $ return ()
            -- Mark the problem as solved.
            modify_ $ \ts ->
              ts{tsSolvedProblems = Map.insert pid (solvedProblem y) (tsSolvedProblems ts)}
          StuckOn (ProblemId boundTo) -> do
            trace ("  STUCK on " ++ show boundTo) $ return ()
            -- If the problem is stuck, re-add it as a dependency of
            -- what it is stuck on.
            void $ addProblem $ Problem ctx m (BoundToProblem boundTo) $
              ("Stuck on" PP.<+> PP.pretty pid) PP.$$ PP.nest 2 (description)
