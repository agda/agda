{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Context where

import Control.Monad.Reader
import Control.Monad.State

import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Scope.Monad (getLocalVars, setLocalVars)

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Open
import Agda.TypeChecking.Monad.Options

import Agda.Utils.Except ( MonadError(catchError) )
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List ((!!!), downFrom)
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty
import Agda.Utils.Size

import Agda.Utils.Impossible
#include "undefined.h"

-- * Modifying the context

-- | Modify a 'Context' in a computation.
{-# SPECIALIZE modifyContext :: (Context -> Context) -> TCM a -> TCM a #-}
modifyContext :: MonadTCM tcm => (Context -> Context) -> tcm a -> tcm a
modifyContext f = local $ \e -> e { envContext = f $ envContext e }

-- | Change to top (=empty) context. Resets the checkpoints.
{-# SPECIALIZE inTopContext :: TCM a -> TCM a #-}
safeInTopContext :: MonadTCM tcm => tcm a -> tcm a
safeInTopContext cont = do
  locals <- liftTCM $ getLocalVars
  liftTCM $ setLocalVars []
  a <- modifyContext (const [])
        $ locally eCurrentCheckpoint (const 0)
        $ locally eCheckpoints (const $ Map.singleton 0 IdS) cont
  liftTCM $ setLocalVars locals
  return a

-- | Change to top (=empty) context, but don't update the checkpoints. Totally
--   not safe!
{-# SPECIALIZE inTopContext :: TCM a -> TCM a #-}
inTopContext :: MonadTCM tcm => tcm a -> tcm a
inTopContext cont = do
  locals <- liftTCM $ getLocalVars
  liftTCM $ setLocalVars []
  a <- modifyContext (const []) cont
  liftTCM $ setLocalVars locals
  return a

-- | Delete the last @n@ bindings from the context.
--
--   Doesn't update checkpoints!! Use `updateContext rho (drop n)` instead,
--   for an appropriate substitution `rho`.
{-# SPECIALIZE escapeContext :: Int -> TCM a -> TCM a #-}
escapeContext :: MonadTCM tcm => Int -> tcm a -> tcm a
escapeContext n = modifyContext $ drop n

-- * Manipulating checkpoints --

-- | Add a new checkpoint. Do not use directly!
checkpoint :: (MonadDebug tcm, MonadTCM tcm) => Substitution -> tcm a -> tcm a
checkpoint sub k = do
  unlessDebugPrinting $ reportSLn "tc.cxt.checkpoint" 105 $ "New checkpoint {"
  old     <- view eCurrentCheckpoint
  oldMods <- use  stModuleCheckpoints
  chkpt <- fresh
  unlessDebugPrinting $ verboseS "tc.cxt.checkpoint" 105 $ do
    cxt <- getContextTelescope
    cps <- view eCheckpoints
    let cps' = Map.insert chkpt IdS $ fmap (applySubst sub) cps
        prCps cps = vcat [ pshow c <+> text ": " <+> pretty s | (c, s) <- Map.toList cps ]
    reportSDoc "tc.cxt.checkpoint" 105 $ return $ nest 2 $ vcat
      [ text "old =" <+> pshow old
      , text "new =" <+> pshow chkpt
      , text "sub =" <+> pretty sub
      , text "cxt =" <+> pretty cxt
      , text "old substs =" <+> prCps cps
      , text "new substs =" <?> prCps cps'
      ]
  x <- flip local k $ \ env -> env
    { envCurrentCheckpoint = chkpt
    , envCheckpoints       = Map.insert chkpt IdS $
                              fmap (applySubst sub) (envCheckpoints env)
    }
  newMods <- use stModuleCheckpoints
  -- Set the checkpoint for introduced modules to the old checkpoint when the
  -- new one goes out of scope. #2897: This isn't actually sound for modules
  -- created under refined parent parameters, but as long as those modules
  -- aren't named we shouldn't look at the checkpoint. The right thing to do
  -- would be to not store these modules in the checkpoint map, but todo..
  stModuleCheckpoints .= Map.union oldMods (old <$ Map.difference newMods oldMods)
  unlessDebugPrinting $ reportSLn "tc.cxt.checkpoint" 105 "}"
  return x

-- | Update the context. Requires a substitution from the old context to the
--   new.
updateContext :: (MonadDebug tcm, MonadTCM tcm) => Substitution -> (Context -> Context) -> tcm a -> tcm a
updateContext sub f = modifyContext f . checkpoint sub

-- | Get the substitution from the context at a given checkpoint to the current context.
checkpointSubstitution :: MonadReader TCEnv tcm => CheckpointId -> tcm Substitution
checkpointSubstitution chkpt =
  caseMaybeM (view (eCheckpoints . key chkpt)) __IMPOSSIBLE__ return

-- | Get substitution @Γ ⊢ ρ : Γm@ where @Γ@ is the current context
--   and @Γm@ is the module parameter telescope of module @m@.
--
--   In case the we don't have a checkpoint for @m@ we return the identity
--   substitution.
--   This is ok for instance if we are outside module @m@ (in which case we
--   have to supply all module parameters to any symbol defined within @m@ we
--   want to refer).
getModuleParameterSub :: (MonadReader TCEnv m, ReadTCState m) => ModuleName -> m Substitution
getModuleParameterSub m = do
  mcp <- (^. stModuleCheckpoints . key m) <$> getTCState
  maybe (return IdS) checkpointSubstitution mcp


-- * Adding to the context

-- | @addCtx x arg cont@ add a variable to the context.
--
--   Chooses an unused 'Name'.
--
--   Warning: Does not update module parameter substitution!
{-# SPECIALIZE addCtx :: Name -> Dom Type -> TCM a -> TCM a #-}
addCtx :: (MonadDebug tcm, MonadTCM tcm) => Name -> Dom Type -> tcm a -> tcm a
addCtx x a ret = do
  let ce = (x,) <$> a
  updateContext (raiseS 1) (ce :) ret
      -- let-bindings keep track of own their context

-- | Pick a concrete name that doesn't shadow anything in the given list.
unshadowedName :: [Name] -> Name -> Name
unshadowedName xs x = head $ filter (notTaken $ map nameConcrete xs)
                           $ iterate nextName x
  where
    notTaken xs x = isNoName x || nameConcrete x `notElem` xs

-- | Pick a concrete name that doesn't shadow anything in the context.
unshadowName :: MonadTCM tcm => Name -> tcm Name
unshadowName x = do
  ctx <- map (fst . unDom) <$> getContext
  return $ unshadowedName ctx x

-- | Various specializations of @addCtx@.
{-# SPECIALIZE addContext :: b -> TCM a -> TCM a #-}
class AddContext b where
  addContext :: (MonadTCM tcm, MonadDebug tcm) => b -> tcm a -> tcm a
  contextSize :: b -> Nat

-- | Wrapper to tell 'addContext not to 'unshadowName's. Used when adding a
--   user-provided, but already type checked, telescope to the context.
newtype KeepNames a = KeepNames a

instance {-# OVERLAPPABLE #-} AddContext a => AddContext [a] where
  addContext = flip (foldr addContext)
  contextSize = sum . map contextSize

instance AddContext (Name, Dom Type) where
  addContext = uncurry addCtx
  contextSize _ = 1

instance AddContext (Dom (Name, Type)) where
  addContext = addContext . distributeF
  contextSize _ = 1

instance AddContext (Dom (String, Type)) where
  addContext = addContext . distributeF
  contextSize _ = 1

instance AddContext ([Name], Dom Type) where
  addContext (xs, dom) = addContext (bindsToTel' id xs dom)
  contextSize (xs, _) = length xs

instance AddContext ([WithHiding Name], Dom Type) where
  addContext ([]                 , dom) = id
  addContext (WithHiding h x : xs, dom) =
    addContext (x , mapHiding (mappend h) dom) .
    addContext (xs, raise 1 dom)
  contextSize (xs, _) = length xs

instance AddContext (String, Dom Type) where
  addContext (s, dom) ret = do
    x <- unshadowName =<< freshName_ s
    addCtx x dom ret
  contextSize _ = 1

instance AddContext (KeepNames String, Dom Type) where
  addContext (KeepNames s, dom) ret = do
    x <- freshName_ s
    addCtx x dom ret
  contextSize _ = 1

instance AddContext (Dom Type) where
  addContext dom = addContext ("_", dom)
  contextSize _ = 1

instance AddContext Name where
  addContext x = addContext (x, __DUMMY_DOM__)
  contextSize _ = 1

instance {-# OVERLAPPING #-} AddContext String where
  addContext s = addContext (s, __DUMMY_DOM__)
  contextSize _ = 1

instance AddContext (KeepNames Telescope) where
  addContext (KeepNames tel) ret = loop tel where
    loop EmptyTel          = ret
    loop (ExtendTel t tel) = underAbstraction' KeepNames t tel loop
  contextSize (KeepNames tel) = size tel

instance AddContext Telescope where
  addContext tel ret = loop tel where
    loop EmptyTel          = ret
    loop (ExtendTel t tel) = underAbstraction' id t tel loop
  contextSize = size

-- | Go under an abstraction.  Do not extend context in case of 'NoAbs'.
{-# SPECIALIZE underAbstraction :: Subst t a => Dom Type -> Abs a -> (a -> TCM b) -> TCM b #-}
underAbstraction :: (Subst t a, MonadTCM tcm, MonadDebug tcm) => Dom Type -> Abs a -> (a -> tcm b) -> tcm b
underAbstraction = underAbstraction' id

underAbstraction' :: (Subst t a, MonadTCM tcm, MonadDebug tcm, AddContext (name, Dom Type)) =>
                     (String -> name) -> Dom Type -> Abs a -> (a -> tcm b) -> tcm b
underAbstraction' _ _ (NoAbs _ v) k = k v
underAbstraction' wrap t a k = underAbstractionAbs' wrap t a k

-- | Go under an abstraction, treating 'NoAbs' as 'Abs'.
underAbstractionAbs :: (Subst t a, MonadTCM tcm, MonadDebug tcm) => Dom Type -> Abs a -> (a -> tcm b) -> tcm b
underAbstractionAbs = underAbstractionAbs' id

underAbstractionAbs'
  :: (Subst t a, MonadTCM tcm, MonadDebug tcm, AddContext (name, Dom Type))
  => (String -> name) -> Dom Type -> Abs a -> (a -> tcm b) -> tcm b
underAbstractionAbs' wrap t a k = addContext (wrap $ realName $ absName a, t) $ k $ absBody a
  where
    realName s = if isNoName s then "x" else argNameToString s

-- | Go under an abstract without worrying about the type to add to the context.
{-# SPECIALIZE underAbstraction_ :: Subst t a => Abs a -> (a -> TCM b) -> TCM b #-}
underAbstraction_ :: (Subst t a, MonadTCM tcm, MonadDebug tcm) => Abs a -> (a -> tcm b) -> tcm b
underAbstraction_ = underAbstraction __DUMMY_DOM__

getLetBindings :: MonadTCM tcm => tcm [(Name,(Term,Dom Type))]
getLetBindings = do
  bs <- asks envLetBindings
  forM (Map.toList bs) $ \ (n,o) -> (,) n <$> getOpen o

-- | Add a let bound variable
{-# SPECIALIZE addLetBinding' :: Name -> Term -> Dom Type -> TCM a -> TCM a #-}
addLetBinding' :: MonadTCM tcm => Name -> Term -> Dom Type -> tcm a -> tcm a
addLetBinding' x v t ret = do
    vt <- liftTCM $ makeOpen (v, t)
    flip local ret $ \e -> e { envLetBindings = Map.insert x vt $ envLetBindings e }

-- | Add a let bound variable
{-# SPECIALIZE addLetBinding :: ArgInfo -> Name -> Term -> Type -> TCM a -> TCM a #-}
addLetBinding :: MonadTCM tcm => ArgInfo -> Name -> Term -> Type -> tcm a -> tcm a
addLetBinding info x v t0 ret = addLetBinding' x v (defaultArgDom info t0) ret


-- * Querying the context

-- | Get the current context.
{-# SPECIALIZE getContext :: TCM [Dom (Name, Type)] #-}
getContext :: MonadReader TCEnv m => m [Dom (Name, Type)]
getContext = asks envContext

-- | Get the size of the current context.
{-# SPECIALIZE getContextSize :: TCM Nat #-}
getContextSize :: (Applicative m, MonadReader TCEnv m) => m Nat
getContextSize = length <$> asks envContext

-- | Generate @[var (n - 1), ..., var 0]@ for all declarations in the context.
{-# SPECIALIZE getContextArgs :: TCM Args #-}
getContextArgs :: (Applicative m, MonadReader TCEnv m) => m Args
getContextArgs = reverse . zipWith mkArg [0..] <$> getContext
  where mkArg i dom = var i <$ argFromDom dom

-- | Generate @[var (n - 1), ..., var 0]@ for all declarations in the context.
{-# SPECIALIZE getContextTerms :: TCM [Term] #-}
getContextTerms :: (Applicative m, MonadReader TCEnv m) => m [Term]
getContextTerms = map var . downFrom <$> getContextSize

-- | Get the current context as a 'Telescope'.
{-# SPECIALIZE getContextTelescope :: TCM Telescope #-}
getContextTelescope :: (Applicative m, MonadReader TCEnv m) => m Telescope
getContextTelescope = telFromList' nameToArgName . reverse <$> getContext

-- | Get the names of all declarations in the context.
{-# SPECIALIZE getContextNames :: TCM [Name] #-}
getContextNames :: (Applicative m, MonadReader TCEnv m) => m [Name]
getContextNames = map (fst . unDom) <$> getContext

-- | get type of bound variable (i.e. deBruijn index)
--
{-# SPECIALIZE lookupBV :: Nat -> TCM (Dom (Name, Type)) #-}
lookupBV :: MonadReader TCEnv m => Nat -> m (Dom (Name, Type))
lookupBV n = do
  ctx <- getContext
  let failure = fail $ "de Bruijn index out of scope: " ++ show n ++
                       " in context " ++ prettyShow (map (fst . unDom) ctx)
  maybe failure (return . fmap (raise $ n + 1)) $ ctx !!! n

{-# SPECIALIZE typeOfBV' :: Nat -> TCM (Dom Type) #-}
typeOfBV' :: (Applicative m, MonadReader TCEnv m) => Nat -> m (Dom Type)
typeOfBV' n = fmap snd <$> lookupBV n

{-# SPECIALIZE typeOfBV :: Nat -> TCM Type #-}
typeOfBV :: (Applicative m, MonadReader TCEnv m) => Nat -> m Type
typeOfBV i = unDom <$> typeOfBV' i

{-# SPECIALIZE nameOfBV :: Nat -> TCM Name #-}
nameOfBV :: (Applicative m, MonadReader TCEnv m) => Nat -> m Name
nameOfBV n = fst . unDom <$> lookupBV n

-- | Get the term corresponding to a named variable. If it is a lambda bound
--   variable the deBruijn index is returned and if it is a let bound variable
--   its definition is returned.
{-# SPECIALIZE getVarInfo :: Name -> TCM (Term, Dom Type) #-}
getVarInfo :: MonadReader TCEnv m => Name -> m (Term, Dom Type)
getVarInfo x =
    do  ctx <- getContext
        def <- asks envLetBindings
        case List.findIndex ((==x) . fst . unDom) ctx of
            Just n -> do
                t <- typeOfBV' n
                return (var n, t)
            _       ->
                case Map.lookup x def of
                    Just vt -> getOpen vt
                    _       -> fail $ "unbound variable " ++ prettyShow (nameConcrete x) ++
                                " (id: " ++ show (nameId x) ++ ")"
