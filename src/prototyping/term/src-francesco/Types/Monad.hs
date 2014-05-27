module Types.Monad
    ( -- * Monad definition
      TC
    , ClosedTC
    , runTC
      -- * Operations
      -- ** Errors
    , typeError
      -- ** Source location
    , atSrcLoc
      -- ** Getting the 'Signature'
    , getSignature
      -- ** Definition handling
    , addDefinition
    , getDefinition
      -- ** MetaVar handling
    , addFreshMetaVar
    , addFreshMetaVar_
    , instantiateMetaVar
    , getTypeOfMetaVar
    , getBodyOfMetaVar
      -- ** Context handling
    , liftClosed
    , extendContext
    , getTypeOfName
    , getTypeOfVar
    , closeClauseBody

      -- * Utils
      -- ** Context operations
    , ctxVars
    , ctxPi
    , ctxApp
    , ctxLam
    ) where

import Prelude                                    hiding (abs, pi)

import           Data.Functor                     ((<$>))
import           Control.Monad.State              (get, gets, modify)
import qualified Data.Map as Map
import           Bound                            hiding (instantiate, abstract)
import           Control.Applicative              (Applicative)
import           Control.Monad.State              (MonadState, State, evalState)
import           Control.Monad.Reader             (MonadReader, asks, local, ReaderT(ReaderT), runReaderT)
import           Control.Monad.Error              (MonadError, throwError, Error, strMsg, ErrorT, runErrorT)
import           Data.Void                        (Void)

import           Syntax.Abstract                  (Name, SrcLoc, noSrcLoc, HasSrcLoc, srcLoc)
import           Syntax.Abstract.Pretty           ()
import           Types.Definition
import           Types.Var
import           Types.Term
import qualified Types.Context                    as Ctx

-- Monad definition
------------------------------------------------------------------------

newtype TC t v a =
    TC {unTC :: ReaderT (TCEnv t v) (ErrorT TCErr (State (Signature t))) a}
    deriving (Functor, Applicative, Monad, MonadReader (TCEnv t v), MonadState (Signature t), MonadError TCErr)

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

initState :: Signature t
initState = Signature
  { sDefinitions = Map.empty
  , sMetaStore = Map.empty
  }

data TCErr = TCErr SrcLoc String

instance Error TCErr where
  strMsg = TCErr noSrcLoc

instance Show TCErr where
  show (TCErr p s) =
    "Error at " ++ show p ++ ":\n" ++ unlines (map ("  " ++) (lines s))

typeError :: String -> TC t v b
typeError err = do
  loc <- asks teCurrentSrcLoc
  throwError $ TCErr loc err

atSrcLoc :: HasSrcLoc a => a -> TC t v b -> TC t v b
atSrcLoc x = local $ \env -> env { teCurrentSrcLoc = srcLoc x }

-- Definitions operations
------------------------------------------------------------------------

addDefinition :: IsTerm t => Name -> Definition t -> TC t v ()
addDefinition x def' =
    modify $ \s -> s { sDefinitions = Map.insert x def' $ sDefinitions s }

getDefinition :: IsTerm t => Name -> TC t v (Definition t)
getDefinition name = atSrcLoc name $ do
  sig <- gets sDefinitions
  case Map.lookup name sig of
    Just def' -> return def'
    Nothing   -> typeError $ "definitionOf: Not in scope " ++ error "TODO definitionOf show name"

-- MetaVar operations
------------------------------------------------------------------------

addFreshMetaVar :: IsTerm t => Type t v -> TC t v (MetaVar, Term t v)
addFreshMetaVar type_ = do
    ctx <- asks teContext
    let mvType = ctxPi ctx type_
    mv <- nextMetaVar
    modify $ \s -> s { sMetaStore = Map.insert mv (Open mvType) $ sMetaStore s }
    return (mv, ctxApp (metaVar mv) ctx)
  where
    nextMetaVar = do
        m <- gets $ Map.maxViewWithKey . sMetaStore
        return $ case m of
          Nothing                  -> MetaVar 0
          Just ((MetaVar i, _), _) -> MetaVar (i + 1)

addFreshMetaVar_ :: IsTerm t => Type t v -> TC t v (Term t v)
addFreshMetaVar_ type_ = snd <$> addFreshMetaVar type_

instantiateMetaVar :: IsTerm t => MetaVar -> Closed (Term t) -> TC t v ()
instantiateMetaVar mv t = do
  mvInst <- getMetaInst mv
  mvType <- case mvInst of
      Inst _ _    -> typeError $ "instantiateMetaVar: already instantiated."
      Open mvType -> return mvType
  modify $ \s -> s { sMetaStore = Map.insert mv (Inst mvType t) (sMetaStore s) }

getTypeOfMetaVar :: IsTerm t => MetaVar -> TC t v (Closed (Type t))
getTypeOfMetaVar mv = do
    mvInst <- getMetaInst mv
    return $ case mvInst of
      Inst mvType _ -> mvType
      Open mvType   -> mvType

getBodyOfMetaVar :: IsTerm t => MetaVar -> TC t v (Maybe (Closed (Term t)))
getBodyOfMetaVar mv = do
    mvInst <- getMetaInst mv
    return $ case mvInst of
      Inst _ mvBody -> Just mvBody
      Open _        -> Nothing

getMetaInst :: IsTerm t => MetaVar -> TC t v (MetaInst t)
getMetaInst mv = do
  mbMvInst <- gets $ Map.lookup mv . sMetaStore
  case mbMvInst of
      Nothing     -> typeError $ "getMetaInst: non-existent meta " ++ show mv
      Just mvInst -> return mvInst

getSignature :: TC t v (Signature t)
getSignature = get

-- Operations on the context
------------------------------------------------------------------------

liftClosed :: ClosedTC t a -> TC t v a
liftClosed = tcLocal $ \env -> env{teContext = Ctx.Empty}

extendContext
    :: (IsTerm t)
    => Name -> Type t v
    -> (TermVar v -> Ctx.Ctx v (Type t) (TermVar v) -> TC t (TermVar v) a)
    -> TC t v a
extendContext n type_ m =
    tcLocal extend (m (B (named n ())) (Ctx.singleton n type_))
  where
    extend env = env { teContext = Ctx.Snoc (teContext env) (n, type_) }

getTypeOfName :: (IsTerm t) => Name -> TC t v (v, Type t v)
getTypeOfName n = do
    ctx <- asks teContext
    case Ctx.lookupName n ctx of
      Nothing -> typeError $ "Name not in scope " ++ show n
      Just t  -> return t

getTypeOfVar :: (IsTerm t) => v -> TC t v (Type t v)
getTypeOfVar v = do
    ctx <- asks teContext
    return $ Ctx.getVar v ctx

-- TODO this looks very wrong here.  See if you can change the interface
-- to get rid of it.
closeClauseBody :: (IsTerm t) => Term t v -> TC t v (ClauseBody t)
closeClauseBody t = do
    ctx <- asks teContext
    return $ Scope $ fmap (toIntVar ctx) t
  where
    toIntVar ctx v = B $ Ctx.elemIndex v ctx

-- Context
----------

-- | Collects all the variables in the 'Ctx.Ctx'.
ctxVars :: IsTerm t => Ctx.Ctx v0 (Type t) v -> [v]
ctxVars = go
  where
    go :: IsTerm t => Ctx.Ctx v0 (Type t) v -> [v]
    go Ctx.Empty                = []
    go (Ctx.Snoc ctx (name, _)) = boundTermVar name : map F (go ctx)

-- | Applies a 'Term' to all the variables in the context.  The
-- variables are applied from left to right.
ctxApp :: IsTerm t => Term t v -> Ctx.Ctx v0 (Type t) v -> Term t v
ctxApp t ctx0 = eliminate t $ map (Apply . var) $ reverse $ ctxVars ctx0

-- | Creates a 'Pi' type containing all the types in the 'Ctx' and
-- terminating with the provided 't'.
ctxPi :: IsTerm t => Ctx.Ctx v0 (Type t) v -> Type t v -> Type t v0
ctxPi Ctx.Empty                  t = t
ctxPi (Ctx.Snoc ctx (_n, type_)) t = ctxPi ctx $ pi type_ (toAbs t)

-- | Creates a 'Lam' term with as many arguments there are in the
-- 'Ctx.Ctx'.
ctxLam :: IsTerm t => Ctx.Ctx v0 (Type t) v -> Term t v -> Term t v0
ctxLam Ctx.Empty        t = t
ctxLam (Ctx.Snoc ctx _) t = ctxLam ctx $ lam $ toAbs t

-- Pretty printing
------------------

-- instance PP.Pretty (Definition Term) where
--   prettyPrec _ _ = PP.text "TODO pretty Definition"
