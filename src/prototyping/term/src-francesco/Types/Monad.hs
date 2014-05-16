module Types.Monad
    ( -- * 'Term' typeclass
      Term(..)
    , lam
    , pi
    , equal
    , app
    , set
    , var
    , metaVar
    , def
    , whnfView
      -- ** Context operations
    , ctxApp
    , ctxPi
      -- * Monad definition
    , TC
    , ClosedTC
    , runTC
      -- * Operations
      -- ** Errors
    , typeError
      -- ** Source location
    , atSrcLoc
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
import           Types.Term
import           Types.Definition
import qualified Types.Context                    as Ctx

-- Term class
------------------------------------------------------------------------

-- | Operations that a term must implement.  We keep it in this module
-- because in the future this typeclass might include the monad as well
-- (e.g. if we want to do memoization/hash consing, etc.).
class (Functor t, Monad t) => Term t where
    type TermAbs t :: * -> *

    toAbs   :: t (TermVar v) -> TermAbs t v
    fromAbs :: TermAbs t v -> t (TermVar v)

    unview :: TermView (TermAbs t) t v -> t v
    view   :: t v -> TermView (TermAbs t) t v

    -- | Tries to apply the eliminators to the term.  Trows an error when
    -- the term and the eliminators don't match.
    eliminate :: t v -> [Elim t v] -> t v

    whnf :: t v -> TC t v (t v)

lam :: (Term t) => TermAbs t v -> t v
lam body = unview $ Lam body

pi :: (Term t) => t v -> TermAbs t v -> t v
pi domain codomain = unview $ Pi domain codomain

equal :: (Term t) => t v -> t v -> t v -> t v
equal type_ x y = unview $ Equal type_ x y

app :: (Term t) => Head v -> [Elim t v] -> t v
app h elims = unview $ App h elims

set :: (Term t) => t v
set = unview Set

var :: (Term t) => v -> t v
var v = unview (App (Var v) [])

metaVar :: (Term t) => MetaVar -> t v
metaVar mv = unview (App (Meta mv) [])

def :: (Term t) => Name -> t v
def f = unview (App (Def f) [])

whnfView :: (Term t) => t v -> TC t v (TermView (TermAbs t) t v)
whnfView t = view <$> whnf t

-- Context operation
------------------------------------------------------------------------

-- | Applies a 'Term' to all the variables in the context.  The
-- variables are applied from left to right.
ctxApp :: Term t => t v -> Ctx.Ctx v0 t v -> t v
ctxApp t ctx0 = eliminate t $ map (Apply . var) $ reverse $ go ctx0
  where
    go :: Ctx.Ctx v0 t v -> [v]
    go Ctx.Empty                    = []
    go (Ctx.Snoc ctx (name, _type)) = boundTermVar name : map F (go ctx)

-- | Creates a 'Pi' type containing all the types in the 'Ctx' and
-- terminating with the provided 't'.
ctxPi :: Term t => Ctx.Ctx v0 t v -> t v -> t v0
ctxPi Ctx.Empty                  t = t
ctxPi (Ctx.Snoc ctx (_n, type_)) t = ctxPi ctx $ pi type_ (toAbs t)

-- Monad definition
------------------------------------------------------------------------

newtype TC t v a =
    TV {unTC :: ReaderT (TCEnv t v) (ErrorT TCErr (State (TCState t))) a}
    deriving (Functor, Applicative, Monad, MonadReader (TCEnv t v), MonadState (TCState t), MonadError TCErr)

type ClosedTC t = TC t Void

runTC :: ClosedTC t a -> IO (Either TCErr a)
runTC m = return $ flip evalState initState
                 $ runErrorT
                 $ flip runReaderT initEnv
                 $ unTC m

tcLocal :: (TCEnv t v -> TCEnv t v') -> TC t v' a -> TC t v a
tcLocal = error "tcLocal TODO"

data TCEnv t v = TCEnv
    { _teContext       :: !(Ctx.ClosedCtx t v)
    , _teCurrentSrcLoc :: !SrcLoc
    }

initEnv :: TCEnv t Void
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
    = Open (ClosedType t)
    | Inst (ClosedType t) (ClosedTerm t)
--  deriving Show

data TCErr = TCErr SrcLoc String

instance Error TCErr where
  strMsg = TCErr noSrcLoc

instance Show TCErr where
  show (TCErr p s) = show p ++ ": " ++ s

typeError :: String -> TC t v b
typeError err = do
  loc <- asks _teCurrentSrcLoc
  throwError $ TCErr loc err

atSrcLoc :: HasSrcLoc a => a -> TC t v b -> TC t v b
atSrcLoc x = local $ \env -> env { _teCurrentSrcLoc = srcLoc x }

-- Definitions operations
------------------------------------------------------------------------

addDefinition :: Name -> Definition t -> TC t v ()
addDefinition x def =
    modify $ \s -> s { _tsSignature = Map.insert x def $ _tsSignature s }

getDefinition :: Name -> TC t v (Definition t)
getDefinition name = atSrcLoc name $ do
  sig <- gets _tsSignature
  case Map.lookup name sig of
    Just def -> return def
    Nothing  -> typeError $ "definitionOf: Not in scope " ++ error "TODO definitionOf show name"

-- MetaVar operations
------------------------------------------------------------------------

addFreshMetaVar :: Term t => Type t v -> TC t v (t v)
addFreshMetaVar type_ = do
    ctx <- asks _teContext
    let mvType = ctxPi ctx type_
    mv <- nextMetaVar
    modify $ \s -> s { _tsMetaStore = Map.insert mv (Open mvType) $ _tsMetaStore s }
    return $ ctxApp (metaVar mv) ctx
  where
    nextMetaVar = do
        m <- gets $ Map.maxViewWithKey . _tsMetaStore
        return $ case m of
          Nothing                  -> MetaVar 0
          Just ((MetaVar i, _), _) -> MetaVar (i + 1)

instantiateMetaVar :: MetaVar -> ClosedTerm t -> TC t v ()
instantiateMetaVar mv t = do
  mvInst <- getMetaInst mv
  mvType <- case mvInst of
      Inst _ _    -> typeError $ "instantiateMetaVar: already instantiated."
      Open mvType -> return mvType
  modify $ \s -> s { _tsMetaStore = Map.insert mv (Inst mvType t) (_tsMetaStore s) }

getTypeOfMetaVar :: MetaVar -> TC t v (ClosedType t)
getTypeOfMetaVar mv = do
    mvInst <- getMetaInst mv
    return $ case mvInst of
      Inst mvType _ -> mvType
      Open mvType   -> mvType

getBodyOfMetaVar :: MetaVar -> TC t v (Maybe (ClosedTerm t))
getBodyOfMetaVar mv = do
    mvInst <- getMetaInst mv
    return $ case mvInst of
      Inst _ mvBody -> Just mvBody
      Open _        -> Nothing

getMetaInst :: MetaVar -> TC t v (MetaInst t)
getMetaInst mv = do
  mbMvInst <- gets $ Map.lookup mv . _tsMetaStore
  case mbMvInst of
      Nothing     -> typeError $ "getMetaInst: non-existent meta " ++ show mv
      Just mvInst -> return mvInst

-- Operations on the context
------------------------------------------------------------------------

extendContext :: Name -> Type t v
              -> (TermVar v -> Ctx.Ctx v t (TermVar v) -> TC t (TermVar v) a)
              -> TC t v a
extendContext n type_ m =
    tcLocal extend (m (B (named n ())) (Ctx.singleton n type_))
  where
    extend env = env { _teContext = Ctx.Snoc (_teContext env) (n, type_) }

getTypeOfName :: Functor t => Name -> TC t v (Maybe (v, Type t v))
getTypeOfName n = do
    ctx <- asks _teContext
    return $ Ctx.lookup n ctx

-- TODO this looks very wrong here.  See if you can change the interface
-- to get rid of it.
closeClauseBody :: Monad t => t v -> TC t v (ClauseBody t)
closeClauseBody t = do
    ctx <- asks _teContext
    return $ Scope $ liftM (toIntVar ctx) t
  where
    toIntVar ctx v = B $ Ctx.elemIndex v ctx
