{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Agda.TypeChecking.Monad.Context where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Control  ( MonadTransControl(..), liftThrough )
import Control.Monad.Trans.Maybe
import Control.Monad.Writer
-- Control.Monad.Fail import is redundant since GHC 8.8.1
import Control.Monad.Fail (MonadFail)

import qualified Data.List as List
import qualified Data.Map as Map

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name (NameInScope(..), LensInScope(..), nameRoot, nameToRawName)
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Free
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Open
import Agda.TypeChecking.Monad.State

import Agda.Utils.Empty
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List ((!!!), downFrom)
import Agda.Utils.ListT
import Agda.Utils.List1 (List1, pattern (:|))
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Pretty
import Agda.Utils.Size

import Agda.Utils.Impossible

-- * Modifying the context

-- | Modify a 'Context' in a computation.  Warning: does not update
--   the checkpoints. Use @updateContext@ instead.
{-# SPECIALIZE unsafeModifyContext :: (Context -> Context) -> TCM a -> TCM a #-}
unsafeModifyContext :: MonadTCEnv tcm => (Context -> Context) -> tcm a -> tcm a
unsafeModifyContext f = localTC $ \e -> e { envContext = f $ envContext e }

-- | Modify the 'Dom' part of context entries.
modifyContextInfo :: MonadTCEnv tcm => (forall e. Dom e -> Dom e) -> tcm a -> tcm a
modifyContextInfo f = unsafeModifyContext $ map f

-- | Change to top (=empty) context. Resets the checkpoints.
{-# SPECIALIZE inTopContext :: TCM a -> TCM a #-}
inTopContext :: (MonadTCEnv tcm, ReadTCState tcm) => tcm a -> tcm a
inTopContext cont =
  unsafeModifyContext (const [])
        $ locallyTC eCurrentCheckpoint (const 0)
        $ locallyTC eCheckpoints (const $ Map.singleton 0 IdS)
        $ locallyTCState stModuleCheckpoints (const Map.empty)
        $ locallyScope scopeLocals (const [])
        $ locallyTC eLetBindings (const Map.empty)
        $ cont

-- | Change to top (=empty) context, but don't update the checkpoints. Totally
--   not safe!
{-# SPECIALIZE unsafeInTopContext :: TCM a -> TCM a #-}
unsafeInTopContext :: (MonadTCEnv m, ReadTCState m) => m a -> m a
unsafeInTopContext cont =
  locallyScope scopeLocals (const []) $
    unsafeModifyContext (const []) cont

-- | Delete the last @n@ bindings from the context.
--
--   Doesn't update checkpoints! Use `escapeContext` or `updateContext
--   rho (drop n)` instead, for an appropriate substitution `rho`.
{-# SPECIALIZE unsafeEscapeContext :: Int -> TCM a -> TCM a #-}
unsafeEscapeContext :: MonadTCM tcm => Int -> tcm a -> tcm a
unsafeEscapeContext n = unsafeModifyContext $ drop n

-- | Delete the last @n@ bindings from the context. Any occurrences of
-- these variables are replaced with the given @err@.
escapeContext :: MonadAddContext m => Empty -> Int -> m a -> m a
escapeContext err n = updateContext (strengthenS err n) $ drop n

-- * Manipulating checkpoints --

-- | Add a new checkpoint. Do not use directly!
checkpoint
  :: (MonadDebug tcm, MonadTCM tcm, MonadFresh CheckpointId tcm, ReadTCState tcm)
  => Substitution -> tcm a -> tcm a
checkpoint sub k = do
  unlessDebugPrinting $ reportSLn "tc.cxt.checkpoint" 105 $ "New checkpoint {"
  old     <- viewTC eCurrentCheckpoint
  oldMods <- useTC  stModuleCheckpoints
  chkpt <- fresh
  unlessDebugPrinting $ verboseS "tc.cxt.checkpoint" 105 $ do
    cxt <- getContextTelescope
    cps <- viewTC eCheckpoints
    let cps' = Map.insert chkpt IdS $ fmap (applySubst sub) cps
        prCps cps = vcat [ pshow c <+> ": " <+> pretty s | (c, s) <- Map.toList cps ]
    reportSDoc "tc.cxt.checkpoint" 105 $ return $ nest 2 $ vcat
      [ "old =" <+> pshow old
      , "new =" <+> pshow chkpt
      , "sub =" <+> pretty sub
      , "cxt =" <+> pretty cxt
      , "old substs =" <+> prCps cps
      , "new substs =" <?> prCps cps'
      ]
  x <- flip localTC k $ \ env -> env
    { envCurrentCheckpoint = chkpt
    , envCheckpoints       = Map.insert chkpt IdS $
                              fmap (applySubst sub) (envCheckpoints env)
    }
  newMods <- useTC stModuleCheckpoints
  -- Set the checkpoint for introduced modules to the old checkpoint when the
  -- new one goes out of scope. #2897: This isn't actually sound for modules
  -- created under refined parent parameters, but as long as those modules
  -- aren't named we shouldn't look at the checkpoint. The right thing to do
  -- would be to not store these modules in the checkpoint map, but todo..
  stModuleCheckpoints `setTCLens` Map.union oldMods (old <$ Map.difference newMods oldMods)
  unlessDebugPrinting $ reportSLn "tc.cxt.checkpoint" 105 "}"
  return x

-- | Get the substitution from the context at a given checkpoint to the current context.
checkpointSubstitution :: MonadTCEnv tcm => CheckpointId -> tcm Substitution
checkpointSubstitution = maybe __IMPOSSIBLE__ return <=< checkpointSubstitution'

-- | Get the substitution from the context at a given checkpoint to the current context.
checkpointSubstitution' :: MonadTCEnv tcm => CheckpointId -> tcm (Maybe Substitution)
checkpointSubstitution' chkpt = viewTC (eCheckpoints . key chkpt)

-- | Get substitution @Γ ⊢ ρ : Γm@ where @Γ@ is the current context
--   and @Γm@ is the module parameter telescope of module @m@.
--
--   Returns @Nothing@ in case the we don't have a checkpoint for @m@.
getModuleParameterSub :: (MonadTCEnv m, ReadTCState m) => ModuleName -> m (Maybe Substitution)
getModuleParameterSub m = do
  mcp <- (^. stModuleCheckpoints . key m) <$> getTCState
  traverse checkpointSubstitution mcp


-- * Adding to the context

{-# SPECIALIZE addCtx :: Name -> Dom Type -> TCM a -> TCM a #-}
class MonadTCEnv m => MonadAddContext m where
  -- | @addCtx x arg cont@ add a variable to the context.
  --
  --   Chooses an unused 'Name'.
  --
  --   Warning: Does not update module parameter substitution!
  addCtx :: Name -> Dom Type -> m a -> m a

  -- | Add a let bound variable to the context
  addLetBinding' :: Name -> Term -> Dom Type -> m a -> m a

  -- | Update the context.
  --   Requires a substitution that transports things living in the old context
  --   to the new.
  updateContext :: Substitution -> (Context -> Context) -> m a -> m a

  withFreshName :: Range -> ArgName -> (Name -> m a) -> m a

  default addCtx
    :: (MonadAddContext n, MonadTransControl t, t n ~ m)
    => Name -> Dom Type -> m a -> m a
  addCtx x a = liftThrough $ addCtx x a

  default addLetBinding'
    :: (MonadAddContext n, MonadTransControl t, t n ~ m)
    => Name -> Term -> Dom Type -> m a -> m a
  addLetBinding' x u a = liftThrough $ addLetBinding' x u a

  default updateContext
    :: (MonadAddContext n, MonadTransControl t, t n ~ m)
    => Substitution -> (Context -> Context) -> m a -> m a
  updateContext sub f = liftThrough $ updateContext sub f

  default withFreshName
    :: (MonadAddContext n, MonadTransControl t, t n ~ m)
    => Range -> ArgName -> (Name -> m a) -> m a
  withFreshName r x cont = do
    st <- liftWith $ \ run -> do
      withFreshName r x $ run . cont
    restoreT $ return st

-- | Default implementation of addCtx in terms of updateContext
defaultAddCtx :: MonadAddContext m => Name -> Dom Type -> m a -> m a
defaultAddCtx x a ret = do
  q <- viewTC eQuantity
  let ce = (x,) <$> inverseApplyQuantity q a
  updateContext (raiseS 1) (ce :) ret

withFreshName_ :: (MonadAddContext m) => ArgName -> (Name -> m a) -> m a
withFreshName_ = withFreshName noRange

instance MonadAddContext m => MonadAddContext (MaybeT m)
instance MonadAddContext m => MonadAddContext (ExceptT e m)
instance MonadAddContext m => MonadAddContext (ReaderT r m)
instance MonadAddContext m => MonadAddContext (StateT r m)
instance (Monoid w, MonadAddContext m) => MonadAddContext (WriterT w m)
deriving instance MonadAddContext m => MonadAddContext (BlockT m)

instance MonadAddContext m => MonadAddContext (ListT m) where
  addCtx x a             = liftListT $ addCtx x a
  addLetBinding' x u a   = liftListT $ addLetBinding' x u a
  updateContext sub f    = liftListT $ updateContext sub f
  withFreshName r x cont = ListT $ withFreshName r x $ runListT . cont

-- | Run the given TCM action, and register the given variable as
--   being shadowed by all the names with the same root that are added
--   to the context during this TCM action.
withShadowingNameTCM :: Name -> TCM b -> TCM b
withShadowingNameTCM x f = do
  reportSDoc "tc.cxt.shadowing" 80 $ pure $ "registered" <+> pretty x <+> "for shadowing"
  when (isInScope x == InScope) $ tellUsedName x
  (result , useds) <- listenUsedNames f
  reportSDoc "tc.cxt.shadowing" 90 $ pure $ "all used names: " <+> text (show useds)
  tellShadowing x useds
  return result

    where
      listenUsedNames f = do
        origUsedNames <- useTC stUsedNames
        setTCLens stUsedNames Map.empty
        result <- f
        newUsedNames <- useTC stUsedNames
        setTCLens stUsedNames $ Map.unionWith (++) origUsedNames newUsedNames
        return (result , newUsedNames)

      tellUsedName x = do
        let concreteX = nameConcrete x
            rawX      = nameToRawName concreteX
            rootX     = nameRoot concreteX
        modifyTCLens (stUsedNames . key rootX) $ Just . (rawX:) . concat

      tellShadowing x useds = case Map.lookup (nameRoot $ nameConcrete x) useds of
        Just shadows -> do
          reportSDoc "tc.cxt.shadowing" 80 $ pure $ "names shadowing" <+> pretty x <+> ": " <+> prettyList_ (map pretty shadows)
          modifyTCLens stShadowingNames $ Map.insertWith (++) x shadows
        Nothing      -> return ()

instance MonadAddContext TCM where
  addCtx x a ret = applyUnless (isNoName x) (withShadowingNameTCM x) $
    defaultAddCtx x a ret

  addLetBinding' x u a ret = applyUnless (isNoName x) (withShadowingNameTCM x) $
    defaultAddLetBinding' x u a ret

  updateContext sub f = unsafeModifyContext f . checkpoint sub

  withFreshName r x m = freshName r x >>= m

addRecordNameContext
  :: (MonadAddContext m, MonadFresh NameId m)
  => Dom Type -> m b -> m b
addRecordNameContext dom ret = do
  x <- setNotInScope <$> freshRecordName
  addCtx x dom ret

-- | Various specializations of @addCtx@.
{-# SPECIALIZE addContext :: b -> TCM a -> TCM a #-}
class AddContext b where
  addContext :: (MonadAddContext m) => b -> m a -> m a
  contextSize :: b -> Nat

-- | Wrapper to tell 'addContext' not to mark names as
--   'NotInScope'. Used when adding a user-provided, but already type
--   checked, telescope to the context.
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

instance AddContext (List1 Name, Dom Type) where
  addContext (xs, dom) = addContext (bindsToTel'1 id xs dom)
  contextSize (xs, _) = length xs

instance AddContext ([WithHiding Name], Dom Type) where
  addContext ([]    , dom) = id
  addContext (x : xs, dom) = addContext (x :| xs, dom)
  contextSize (xs, _) = length xs

instance AddContext (List1 (WithHiding Name), Dom Type) where
  addContext (WithHiding h x :| xs, dom) =
    addContext (x , mapHiding (mappend h) dom) .
    addContext (xs, raise 1 dom)
  contextSize (xs, _) = length xs

instance AddContext ([Arg Name], Type) where
  addContext (xs, t) = addContext ((map . fmap) unnamed xs :: [NamedArg Name], t)
  contextSize (xs, _) = length xs

instance AddContext (List1 (Arg Name), Type) where
  addContext (xs, t) = addContext ((fmap . fmap) unnamed xs :: List1 (NamedArg Name), t)
  contextSize (xs, _) = length xs

instance AddContext ([NamedArg Name], Type) where
  addContext ([], _)     = id
  addContext (x : xs, t) = addContext (x :| xs, t)
  contextSize (xs, _) = length xs

instance AddContext (List1 (NamedArg Name), Type) where
  addContext (x :| xs, t) =
    addContext (namedArg x, t <$ domFromNamedArgName x) .
    addContext (xs, raise 1 t)
  contextSize (xs, _) = length xs

instance AddContext (String, Dom Type) where
  addContext (s, dom) ret =
    withFreshName noRange s $ \x -> addCtx (setNotInScope x) dom ret
  contextSize _ = 1

instance AddContext (KeepNames String, Dom Type) where
  addContext (KeepNames s, dom) ret =
    withFreshName noRange s $ \ x -> addCtx x dom ret
  contextSize _ = 1

instance AddContext (Dom Type) where
  addContext dom = addContext ("_" :: String, dom)
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
{-# SPECIALIZE underAbstraction :: Subst a => Dom Type -> Abs a -> (a -> TCM b) -> TCM b #-}
underAbstraction :: (Subst a, MonadAddContext m) => Dom Type -> Abs a -> (a -> m b) -> m b
underAbstraction = underAbstraction' id

underAbstraction' :: (Subst a, MonadAddContext m, AddContext (name, Dom Type)) =>
                     (String -> name) -> Dom Type -> Abs a -> (a -> m b) -> m b
underAbstraction' _ _ (NoAbs _ v) k = k v
underAbstraction' wrap t a k = underAbstractionAbs' wrap t a k

-- | Go under an abstraction, treating 'NoAbs' as 'Abs'.
underAbstractionAbs :: (Subst a, MonadAddContext m) => Dom Type -> Abs a -> (a -> m b) -> m b
underAbstractionAbs = underAbstractionAbs' id

underAbstractionAbs'
  :: (Subst a, MonadAddContext m, AddContext (name, Dom Type))
  => (String -> name) -> Dom Type -> Abs a -> (a -> m b) -> m b
underAbstractionAbs' wrap t a k = addContext (wrap $ realName $ absName a, t) $ k $ absBody a
  where
    realName s = if isNoName s then "x" else argNameToString s

-- | Go under an abstract without worrying about the type to add to the context.
{-# SPECIALIZE underAbstraction_ :: Subst a => Abs a -> (a -> TCM b) -> TCM b #-}
underAbstraction_ :: (Subst a, MonadAddContext m) => Abs a -> (a -> m b) -> m b
underAbstraction_ = underAbstraction __DUMMY_DOM__

-- | Map a monadic function on the thing under the abstraction, adding
--   the abstracted variable to the context.
mapAbstraction
  :: (Subst a, Subst b, MonadAddContext m)
  => Dom Type -> (a -> m b) -> Abs a -> m (Abs b)
mapAbstraction dom f x = (x $>) <$> underAbstraction dom x f

getLetBindings :: MonadTCM tcm => tcm [(Name,(Term,Dom Type))]
getLetBindings = do
  bs <- asksTC envLetBindings
  forM (Map.toList bs) $ \ (n,o) -> (,) n <$> getOpen o

-- | Add a let bound variable
{-# SPECIALIZE addLetBinding' :: Name -> Term -> Dom Type -> TCM a -> TCM a #-}
defaultAddLetBinding' :: MonadTCEnv m => Name -> Term -> Dom Type -> m a -> m a
defaultAddLetBinding' x v t ret = do
    vt <- makeOpen (v, t)
    flip localTC ret $ \e -> e { envLetBindings = Map.insert x vt $ envLetBindings e }

-- | Add a let bound variable
{-# SPECIALIZE addLetBinding :: ArgInfo -> Name -> Term -> Type -> TCM a -> TCM a #-}
addLetBinding :: MonadAddContext m => ArgInfo -> Name -> Term -> Type -> m a -> m a
addLetBinding info x v t0 ret = addLetBinding' x v (defaultArgDom info t0) ret


-- * Querying the context

-- | Get the current context.
{-# SPECIALIZE getContext :: TCM [Dom (Name, Type)] #-}
getContext :: MonadTCEnv m => m [Dom (Name, Type)]
getContext = asksTC envContext

-- | Get the size of the current context.
{-# SPECIALIZE getContextSize :: TCM Nat #-}
getContextSize :: (Applicative m, MonadTCEnv m) => m Nat
getContextSize = length <$> asksTC envContext

-- | Generate @[var (n - 1), ..., var 0]@ for all declarations in the context.
{-# SPECIALIZE getContextArgs :: TCM Args #-}
getContextArgs :: (Applicative m, MonadTCEnv m) => m Args
getContextArgs = reverse . zipWith mkArg [0..] <$> getContext
  where mkArg i dom = var i <$ argFromDom dom

-- | Generate @[var (n - 1), ..., var 0]@ for all declarations in the context.
{-# SPECIALIZE getContextTerms :: TCM [Term] #-}
getContextTerms :: (Applicative m, MonadTCEnv m) => m [Term]
getContextTerms = map var . downFrom <$> getContextSize

-- | Get the current context as a 'Telescope'.
{-# SPECIALIZE getContextTelescope :: TCM Telescope #-}
getContextTelescope :: (Applicative m, MonadTCEnv m) => m Telescope
getContextTelescope = telFromList' nameToArgName . reverse <$> getContext

-- | Get the names of all declarations in the context.
{-# SPECIALIZE getContextNames :: TCM [Name] #-}
getContextNames :: (Applicative m, MonadTCEnv m) => m [Name]
getContextNames = map (fst . unDom) <$> getContext

-- | get type of bound variable (i.e. deBruijn index)
--
{-# SPECIALIZE lookupBV' :: Nat -> TCM (Maybe (Dom (Name, Type))) #-}
lookupBV' :: MonadTCEnv m => Nat -> m (Maybe (Dom (Name, Type)))
lookupBV' n = do
  ctx <- getContext
  return $ raise (n + 1) <$> ctx !!! n

{-# SPECIALIZE lookupBV :: Nat -> TCM (Dom (Name, Type)) #-}
lookupBV :: (MonadFail m, MonadTCEnv m) => Nat -> m (Dom (Name, Type))
lookupBV n = do
  let failure = do
        ctx <- getContext
        fail $ "de Bruijn index out of scope: " ++ show n ++
               " in context " ++ prettyShow (map (fst . unDom) ctx)
  maybeM failure return $ lookupBV' n

{-# SPECIALIZE domOfBV :: Nat -> TCM (Dom Type) #-}
domOfBV :: (Applicative m, MonadFail m, MonadTCEnv m) => Nat -> m (Dom Type)
domOfBV n = fmap snd <$> lookupBV n

{-# SPECIALIZE typeOfBV :: Nat -> TCM Type #-}
typeOfBV :: (Applicative m, MonadFail m, MonadTCEnv m) => Nat -> m Type
typeOfBV i = unDom <$> domOfBV i

{-# SPECIALIZE nameOfBV' :: Nat -> TCM (Maybe Name) #-}
nameOfBV' :: (Applicative m, MonadFail m, MonadTCEnv m) => Nat -> m (Maybe Name)
nameOfBV' n = fmap (fst . unDom) <$> lookupBV' n

{-# SPECIALIZE nameOfBV :: Nat -> TCM Name #-}
nameOfBV :: (Applicative m, MonadFail m, MonadTCEnv m) => Nat -> m Name
nameOfBV n = fst . unDom <$> lookupBV n

-- | Get the term corresponding to a named variable. If it is a lambda bound
--   variable the deBruijn index is returned and if it is a let bound variable
--   its definition is returned.
{-# SPECIALIZE getVarInfo :: Name -> TCM (Term, Dom Type) #-}
getVarInfo :: (MonadFail m, MonadTCEnv m) => Name -> m (Term, Dom Type)
getVarInfo x =
    do  ctx <- getContext
        def <- asksTC envLetBindings
        case List.findIndex ((==x) . fst . unDom) ctx of
            Just n -> do
                t <- domOfBV n
                return (var n, t)
            _       ->
                case Map.lookup x def of
                    Just vt -> getOpen vt
                    _       -> fail $ "unbound variable " ++ prettyShow (nameConcrete x) ++
                                " (id: " ++ prettyShow (nameId x) ++ ")"
