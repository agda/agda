{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Impl.Monad
    ( -- * Monad definition
      TC
    , runTC
      -- * Operations
      -- ** Errors
    , typeError
      -- ** Definition handling
    , addDefinition
    , getDefinition
      -- ** MetaVar handling
    , addFreshMetaVar
    , instantiateMetaVar
    , getTypeOfMetaVar
    , getBodyOfMetaVar
      -- ** Context handling
    , extendContext
    , getTypeOfName
    , closeClauseBody
      -- ** Source location
    , atSrcLoc
    ) where

import Prelude hiding (pi)

import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Data.Void
import qualified Data.Map as Map
import Bound

import           Syntax.Abstract                  (Name, SrcLoc, noSrcLoc, HasSrcLoc, srcLoc)
import           Term
import           Impl.Term
import           Impl.Definition
import           Impl.Context

------------------------------------------------------------------------

newtype TC v a =
    TV {unTC :: ReaderT (TCEnv v) (ErrorT TCErr (State TCState)) a}
    deriving (Functor, Applicative, Monad, MonadReader (TCEnv v), MonadState TCState, MonadError TCErr)

runTC :: TC Void a -> IO (Either TCErr a)
runTC m = return $ flip evalState initState
                 $ runErrorT
                 $ flip runReaderT initEnv
                 $ unTC m

tcLocal :: (TCEnv v -> TCEnv v') -> TC v' a -> TC v a
tcLocal = error "tcLocal TODO"

data TCEnv v = TCEnv
    { _teContext       :: !(Context Type v)
    , _teCurrentSrcLoc :: !SrcLoc
    }

initEnv :: TCEnv Void
initEnv = TCEnv
  { _teContext       = EmptyContext
  , _teCurrentSrcLoc = noSrcLoc
  }

data TCState = TCState
  { _tsSignature :: Map.Map Name TermDefinition
  , _tsMetaStore :: Map.Map MetaVar MetaInst
  }

initState :: TCState
initState = TCState
  { _tsSignature = Map.empty
  , _tsMetaStore = Map.empty
  }

data MetaInst
    = Open ClosedType
    | Inst ClosedType ClosedTerm
--  deriving Show

data TCErr = TCErr SrcLoc String

instance Error TCErr where
  strMsg = TCErr noSrcLoc

instance Show TCErr where
  show (TCErr p s) = show p ++ ": " ++ s

typeError :: String -> TC v b
typeError err = do
  loc <- asks _teCurrentSrcLoc
  throwError $ TCErr loc err

-- Operations on the state
------------------------------------------------------------------------

addDefinition :: Name -> TermDefinition -> TC v ()
addDefinition x def =
    modify $ \s -> s { _tsSignature = Map.insert x def $ _tsSignature s }

getDefinition :: Name -> TC v TermDefinition
getDefinition name = atSrcLoc name $ do
  sig <- gets _tsSignature
  case Map.lookup name sig of
    Just def -> return def
    Nothing  -> typeError $ "definitionOf: Not in scope " ++ error "TODO definitionOf show name"

addFreshMetaVar :: Type v -> TC v (Term v)
addFreshMetaVar type_ = do
    ctx <- asks _teContext
    let mvType = contextPi ctx type_
    mv <- nextMetaVar
    modify $ \s -> s { _tsMetaStore = Map.insert mv (Open mvType) $ _tsMetaStore s }
    return $ contextApp (App (Meta mv) []) ctx
  where
    nextMetaVar = do
        m <- gets $ Map.maxViewWithKey . _tsMetaStore
        return $ case m of
          Nothing                  -> MetaVar 0
          Just ((MetaVar i, _), _) -> MetaVar (i + 1)

instantiateMetaVar :: MetaVar -> ClosedTerm -> TC v ()
instantiateMetaVar mv t = do
  mvInst <- getMetaInst mv
  mvType <- case mvInst of
      Inst _ _    -> typeError $ "instantiateMeta: already instantiated."
      Open mvType -> return mvType
  modify $ \s -> s { _tsMetaStore = Map.insert mv (Inst mvType t) (_tsMetaStore s) }

getTypeOfMetaVar :: MetaVar -> TC v ClosedType
getTypeOfMetaVar mv = do
    mvInst <- getMetaInst mv
    return $ case mvInst of
      Inst mvType _ -> mvType
      Open mvType   -> mvType

getBodyOfMetaVar :: MetaVar -> TC v (Maybe ClosedTerm)
getBodyOfMetaVar mv = do
    mvInst <- getMetaInst mv
    return $ case mvInst of
      Inst _ mvBody -> Just mvBody
      Open _        -> Nothing

getMetaInst :: MetaVar -> TC v MetaInst
getMetaInst mv = do
  mbMvInst <- gets $ Map.lookup mv . _tsMetaStore
  case mbMvInst of
      Nothing     -> typeError $ "getMetaInst: non-existent meta " ++ show mv
      Just mvInst -> return mvInst

-- Operations on the reader
------------------------------------------------------------------------

extendContext
    :: Name -> Type v
    -> ((v -> TermVar v) -> TermVar v -> TC (TermVar v) a)
    -> TC v a
extendContext n type_ m = tcLocal extend (m F (B (named n ())))
  where
    extend env = env { _teContext = (_teContext env) :< (n, type_) }

getTypeOfName :: Name -> TC v (Maybe (v, Type v))
getTypeOfName n = do
    ctx <- asks _teContext
    return $ contextLookup n ctx

atSrcLoc :: HasSrcLoc a => a -> TC v b -> TC v b
atSrcLoc x = local $ \env -> env { _teCurrentSrcLoc = srcLoc x }

closeClauseBody :: Term v -> TC v ClauseBody
closeClauseBody t = do
    ctx <- asks _teContext
    return $ Scope $ liftM (toIntVar ctx) t
  where
    toIntVar ctx v = B $ contextElemIndex v ctx
