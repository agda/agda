module Types.Monad.Types
    ( -- * Useful type synonyms
      Type
    , Term
      -- * Monad
    , TC
    , runTC
    , ClosedTC
    , TCEnv(..)
    , TCState(..)
    , tcLocal
    , MetaInst(..)
    , typeError
    , atSrcLoc
    ) where

import           Control.Applicative              (Applicative)
import           Control.Monad.State              (MonadState, State, evalState)
import           Control.Monad.Reader             (MonadReader, asks, local, ReaderT(ReaderT), runReaderT)
import           Control.Monad.Error              (MonadError, throwError, Error, strMsg, ErrorT, runErrorT)
import           Data.Void                        (Void)
import qualified Data.Map as Map

import           Syntax.Abstract                  (Name, SrcLoc, noSrcLoc, HasSrcLoc, srcLoc)
import           Syntax.Abstract.Pretty           ()
import           Types.Definition
import           Types.Var
import qualified Types.Context                    as Ctx

-- Useful type synonyms
------------------------------------------------------------------------

type Type (t :: * -> *) = t
type Term (t :: * -> *) = t

-- Monad definition
------------------------------------------------------------------------

newtype TC t v a =
    TC {unTC :: ReaderT (TCEnv t v) (ErrorT TCErr (State (TCState t))) a}
    deriving (Functor, Applicative, Monad, MonadReader (TCEnv t v), MonadState (TCState t), MonadError TCErr)

type ClosedTC t = TC t Void

runTC :: ClosedTC t a -> IO (Either TCErr a)
runTC m = return $ flip evalState initState
                 $ runErrorT
                 $ flip runReaderT initEnv
                 $ unTC m

tcLocal :: (TCEnv t v -> TCEnv t v') -> TC t v' a -> TC t v a
tcLocal f (TC (ReaderT m)) = TC (ReaderT (m . f))

data TCEnv t v = TCEnv
    { _teContext       :: !(Ctx.ClosedCtx t v)
    , _teCurrentSrcLoc :: !SrcLoc
    }

initEnv :: Closed (TCEnv t)
initEnv = TCEnv
  { _teContext       = Ctx.Empty
  , _teCurrentSrcLoc = noSrcLoc
  }

data TCState t = TCState
  { _tsSignature :: Map.Map Name (Definition t)
  , _tsMetaStore :: Map.Map MetaVar (MetaInst t)
  }

initState :: TCState t
initState = TCState
  { _tsSignature = Map.empty
  , _tsMetaStore = Map.empty
  }

data MetaInst t
    = Open (Closed (Type t))
    | Inst (Closed (Type t)) (Closed (Term t))
--  deriving Show

data TCErr = TCErr SrcLoc String

instance Error TCErr where
  strMsg = TCErr noSrcLoc

instance Show TCErr where
  show (TCErr p s) =
    "Error at " ++ show p ++ ":\n" ++ unlines (map ("  " ++) (lines s))

typeError :: String -> TC t v b
typeError err = do
  loc <- asks _teCurrentSrcLoc
  throwError $ TCErr loc err

atSrcLoc :: HasSrcLoc a => a -> TC t v b -> TC t v b
atSrcLoc x = local $ \env -> env { _teCurrentSrcLoc = srcLoc x }
