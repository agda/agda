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
    , ProblemIdInt
    , ProblemState
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
import           Types.Var
import           Types.Term
import           Eval

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
  , trSolvedProblems   :: !(Set.Set ProblemIdInt)
  , trUnsolvedProblems :: !(Map.Map ProblemIdInt (ProblemState, PP.Doc))
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

newtype SolvedProblem = SolvedProblem Dynamic

solvedProblem :: Typeable a => a -> SolvedProblem
solvedProblem = SolvedProblem . toDyn

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

newProblem
    :: (Typeable a, IsVar v, IsTerm t, Nf p, PP.Pretty (p t v))
    => Set.Set MetaVar -> p t v
    -> (Closed (Term t) -> StuckTC t v a) -> TC t v (ProblemId t v a)
newProblem mvs _ _ | Set.null mvs = do
    error "Types.Monad.Base.newProblem: empty set of metas."
newProblem mvs desc m = do
    ctx <- askContext
    prob <- saveSrcLoc $ Problem
      { pContext     = ctx
      , pProblem     = m
      , pState       = BoundToMetaVars mvs
      , pDescription = desc
      }
    addFreshProblem prob

bindProblem
    :: (Typeable a, Typeable b, IsTerm t, IsVar v, Nf p, PP.Pretty (p t v))
    => ProblemId t v a -> p t v -> (a -> StuckTC t v b)
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

waitOnProblem
    :: (Typeable a, Typeable b, IsTerm t, IsVar v', Nf p, PP.Pretty (p t v'))
    => ProblemId t v a -> p t v' -> StuckTC t v' b
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

data StuckProblemDescription p (t :: * -> *) v =
  StuckProblemDescription ProblemIdInt (p t v)

instance (Bound p) => Bound (StuckProblemDescription p) where
  StuckProblemDescription pid t >>>= f = StuckProblemDescription pid (t >>>= f)

instance (Nf p) => Nf (StuckProblemDescription p) where
  nf' sig (StuckProblemDescription pid t) = StuckProblemDescription pid (nf' sig t)

instance (IsVar v, IsTerm t, PP.Pretty (p t v)) => PP.Pretty (StuckProblemDescription p t v) where
  pretty (StuckProblemDescription pid desc) =
    ("Stuck on" PP.<+> PP.pretty pid) PP.$$ PP.nest 2 (PP.pretty desc)

-- TODO improve efficiency of this.
solveProblems :: (IsTerm t) => ClosedTC t ()
solveProblems = do
  unsolvedProbs <- Map.toList . tsUnsolvedProblems <$> get
  progress <- fmap or $ forM unsolvedProbs $ \(pid, (Problem ctx prob state desc)) -> do
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
      Just solved -> do True <$ solveProblem pid desc solved ctx prob
  when progress solveProblems
  where
    solveProblem
      :: (Typeable a, Typeable b, IsTerm t, IsVar v, Nf p, PP.Pretty (p t v))
      => ProblemIdInt -> p t v
      -> SolvedProblem
      -> Ctx.ClosedCtx t v -> (a -> StuckTC t v b)
      -> ClosedTC t ()
    solveProblem pid desc (SolvedProblem x) ctx m = do
      Just x' <- return $ fromDynamic x
      modify_ $ \ts -> ts{tsUnsolvedProblems = Map.delete pid (tsUnsolvedProblems ts)}
      localContext (\_ -> ctx) $ do
        stuck <- m x'
        case stuck of
          NotStuck y -> do
            -- Mark the problem as solved.
            modify_ $ \ts ->
              ts{tsSolvedProblems = Map.insert pid (solvedProblem y) (tsSolvedProblems ts)}
          StuckOn (ProblemId boundTo) -> do
            -- If the problem is stuck, re-add it as a dependency of
            -- what it is stuck on.
            void $ addProblem pid $ Problem ctx m (BoundToProblem boundTo) $
              StuckProblemDescription pid desc
