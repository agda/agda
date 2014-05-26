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
      -- ** Definition handling
    , addDefinition
    , getDefinition
      -- ** MetaVar handling
    , addFreshMetaVar
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
      -- ** Useful synonyms
    , Term
    , Type
      -- ** Context operations
    , ctxVars
    , ctxPi
    , ctxApp
    , ctxLam
    ) where

import Prelude                                    hiding (abs, pi)

import           Control.Monad.State              (gets, modify)
import           Control.Monad.Reader             (asks)
import qualified Data.Map as Map
import           Bound                            hiding (instantiate, abstract)

import           Syntax.Abstract                  (Name)
import           Syntax.Abstract.Pretty           ()
import           Types.Definition
import           Types.Var
import           Types.Term
import qualified Types.Context                    as Ctx
import           Types.Monad.Types

-- Definitions operations
------------------------------------------------------------------------

addDefinition :: IsTerm t => Name -> Definition t -> TC t v ()
addDefinition x def' =
    modify $ \s -> s { _tsSignature = Map.insert x def' $ _tsSignature s }

getDefinition :: IsTerm t => Name -> TC t v (Definition t)
getDefinition name = atSrcLoc name $ do
  sig <- gets _tsSignature
  case Map.lookup name sig of
    Just def' -> return def'
    Nothing   -> typeError $ "definitionOf: Not in scope " ++ error "TODO definitionOf show name"

-- MetaVar operations
------------------------------------------------------------------------

addFreshMetaVar :: IsTerm t => Type t v -> TC t v (Term t v)
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

instantiateMetaVar :: IsTerm t => MetaVar -> Closed (Term t) -> TC t v ()
instantiateMetaVar mv t = do
  mvInst <- getMetaInst mv
  mvType <- case mvInst of
      Inst _ _    -> typeError $ "instantiateMetaVar: already instantiated."
      Open mvType -> return mvType
  modify $ \s -> s { _tsMetaStore = Map.insert mv (Inst mvType t) (_tsMetaStore s) }

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
  mbMvInst <- gets $ Map.lookup mv . _tsMetaStore
  case mbMvInst of
      Nothing     -> typeError $ "getMetaInst: non-existent meta " ++ show mv
      Just mvInst -> return mvInst

-- Operations on the context
------------------------------------------------------------------------

liftClosed :: ClosedTC t a -> TC t v a
liftClosed = tcLocal $ \env -> env{_teContext = Ctx.Empty}

extendContext
    :: (IsTerm t)
    => Name -> Type t v
    -> (TermVar v -> Ctx.Ctx v (Type t) (TermVar v) -> TC t (TermVar v) a)
    -> TC t v a
extendContext n type_ m =
    tcLocal extend (m (B (named n ())) (Ctx.singleton n type_))
  where
    extend env = env { _teContext = Ctx.Snoc (_teContext env) (n, type_) }

getTypeOfName :: (IsTerm t) => Name -> TC t v (v, Type t v)
getTypeOfName n = do
    ctx <- asks _teContext
    case Ctx.lookupName n ctx of
      Nothing -> typeError $ "Name not in scope " ++ show n
      Just t  -> return t

getTypeOfVar :: (IsTerm t) => v -> TC t v (Type t v)
getTypeOfVar v = do
    ctx <- asks _teContext
    return $ Ctx.getVar v ctx

-- TODO this looks very wrong here.  See if you can change the interface
-- to get rid of it.
closeClauseBody :: (IsTerm t) => Term t v -> TC t v (ClauseBody t)
closeClauseBody t = do
    ctx <- asks _teContext
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
