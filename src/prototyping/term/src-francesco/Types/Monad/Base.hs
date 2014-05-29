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
    ) where

import Prelude                                    hiding (abs, pi)

import           Control.Monad.State              (get, put)
import           Control.Applicative              (Applicative)
import           Control.Monad.Trans.State        (State, evalState)
import           Control.Monad.Trans.Reader       (asks, local, ReaderT(ReaderT), runReaderT)
import           Control.Monad.Trans.Error        (throwError, Error, strMsg, ErrorT, runErrorT)
import           Data.Void                        (Void)
import           Control.Monad.Trans.Class        (lift)

import           Syntax.Abstract                  (SrcLoc, noSrcLoc, HasSrcLoc, srcLoc)
import           Syntax.Abstract.Pretty           ()
import qualified Types.Context                    as Ctx
import qualified Types.Signature                  as Sig
import           Types.Var

-- Monad definition
------------------------------------------------------------------------

newtype TC t v a =
    TC {unTC :: ReaderT (TCEnv t v) (ErrorT TCErr (State (Sig.Signature t))) a}
    deriving (Functor, Applicative, Monad)

type ClosedTC t = TC t Void

runTC :: ClosedTC t a -> IO (Either TCErr a)
runTC m = return $ flip evalState Sig.empty
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

data TCErr = TCErr SrcLoc String

instance Error TCErr where
  strMsg = TCErr noSrcLoc

instance Show TCErr where
  show (TCErr p s) =
    "Error at " ++ show p ++ ":\n" ++ unlines (map ("  " ++) (lines s))

-- Errors
------------------------------------------------------------------------

typeError :: String -> TC t v b
typeError err = do
  loc <- TC $ asks teCurrentSrcLoc
  TC $ lift $ throwError $ TCErr loc err

-- SrcLoc
------------------------------------------------------------------------

atSrcLoc :: HasSrcLoc a => a -> TC t v b -> TC t v b
atSrcLoc x (TC m) = TC $ local (\env -> env { teCurrentSrcLoc = srcLoc x }) m

-- Signature
------------------------------------------------------------------------

getSignature :: TC t v (Sig.Signature t)
getSignature = TC $ lift $ lift get

putSignature :: Sig.Signature t -> TC t v ()
putSignature = TC . lift . lift . put

-- Context
------------------------------------------------------------------------

askContext :: TC t v (Ctx.ClosedCtx t v)
askContext = TC $ asks teContext

localContext
    :: (Ctx.ClosedCtx t v -> Ctx.ClosedCtx t v') -> TC t v' a -> TC t v a
localContext f = tcLocal $ \env -> env{teContext = f (teContext env)}
