{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
module Types.Monad where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error

import Syntax.Abstract (Name)

-- TC monad ---------------------------------------------------------------

data TCState r = TCState
  { termState :: TermState r }

initState :: TermRep r => TCState r
initState = TCState
  { termState = error "impossible: no termState"
  }

data TCEnv r = TCEnv
  { context :: Context r }

data ContextEntry r = TypedVar Name (Type r)
                | DefinedVar Name (Type r) (Term r)

initEnv :: TermRep r => TCEnv r
initEnv = TCEnv
  { context = error "impossible: no context"
  }

newtype TC r a = TC { unTC :: ReaderT (TCEnv r) (StateT (TCState r) (ErrorT String IO)) a }
  deriving (Monad, MonadState (TCState r), MonadReader (TCEnv r),
            MonadError String, Functor, Applicative)

runTC :: TermRep r => r -> TC r a -> IO (Either String a)
runTC _ m = runErrorT $ flip evalStateT initState $ flip runReaderT initEnv $ unTC $ do
  ts  <- liftTC initialTermState
  cxt <- liftTC emptyCxt
  modify $ \s -> s { termState = ts }
  local (\e -> e { context = cxt }) m

type Constraints r = [Closure r (Constraint r)]

data Constraint r

data Closure r a = Closure
  { clEnv   :: TCEnv r
  , clValue :: a
  }

extendContext :: TermRep r => ContextEntry r -> TC r a -> TC r a
extendContext e k = do
  oldCxt <- asks context
  newCxt <- liftTC $ extendCxt e oldCxt
  local (\e -> e { context = newCxt }) k

-- Term representation class ----------------------------------------------

class (Applicative (TermMonad r), Monad (TermMonad r), Ord (Var r)) => TermRep r where
  type Type r
  type Term r
  type Var r
  type Context r
  data TermMonad r :: * -> *
  type TermState r

  liftTC :: TermMonad r a -> TC r a
  initialTermState :: TermMonad r (TermState r)

  emptyCxt  :: TermMonad r (Context r)
  lookupCxt :: Name -> Context r -> TermMonad r (Var r, ContextEntry r)
  extendCxt :: ContextEntry r -> Context r -> TermMonad r (Context r)
  updateCxt :: Var r -> ContextEntry r -> Context r -> TermMonad r (Context r)

  mkType :: Term r -> TermMonad r (Type r)
