
module Agda.TypeChecking.Monad.Context where

import Data.Text (Text)
import qualified Data.Text as T

import Control.Monad                ( (<=<), forM, when )
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Control  ( MonadTransControl(..), liftThrough )
import Control.Monad.Trans.Identity ( IdentityT )
import Control.Monad.Trans.Maybe
import Control.Monad.Writer         ( WriterT )

import Data.Foldable
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty
import Agda.Syntax.Concrete.Name (NameInScope(..), LensInScope(..), nameRoot, nameToRawName)
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Open
import Agda.TypeChecking.Monad.State

import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List ((!!!), downFrom)
import Agda.Utils.ListT
import Agda.Utils.List1 (List1, pattern (:|))
import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.Set1 as Set1
import Agda.Utils.Maybe
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.Update

import Agda.Utils.Impossible

-- * Modifying the context

-- | Modify a 'Context' in a computation.  Warning: does not update
--   the checkpoints. Use @updateContext@ instead.
{-# INLINE unsafeModifyContext #-}
unsafeModifyContext :: MonadTCEnv tcm => (Context -> Context) -> tcm a -> tcm a
unsafeModifyContext f = localTC $ \e -> e { envContext = f $ envContext e }

{-# INLINE modifyContextInfo #-}
-- | Modify the 'Dom' part of context entries.
modifyContextInfo :: MonadTCEnv tcm => (forall e. Dom e -> Dom e) -> tcm a -> tcm a
modifyContextInfo f = unsafeModifyContext $ fmap $ \case
    (CtxVar x a)   -> CtxVar x (f a)

-- | Change to top (=empty) context. Resets the checkpoints.
{-# SPECIALIZE inTopContext :: TCM a -> TCM a #-}
inTopContext :: (MonadTCEnv tcm, ReadTCState tcm) => tcm a -> tcm a
inTopContext cont =
  unsafeModifyContext (const CxEmpty)
        $ locallyTC eCurrentCheckpoint (const 0)
        $ locallyTC eCheckpoints (const $ Map.singleton 0 IdS)
        $ locallyScope scopeLocals (const [])
        $ locallyTC eLetBindings (const Map.empty)
        $ withoutModuleCheckpoints
        $ cont

-- | Change to top (=empty) context, but don't update the checkpoints. Totally
--   not safe!
{-# SPECIALIZE unsafeInTopContext :: TCM a -> TCM a #-}
unsafeInTopContext :: (MonadTCEnv m, ReadTCState m) => m a -> m a
unsafeInTopContext cont =
  locallyScope scopeLocals (const []) $
    unsafeModifyContext (const CxEmpty) cont

-- | Delete the last @n@ bindings from the context.
--
--   Doesn't update checkpoints! Use `escapeContext` or `updateContext
--   rho (drop n)` instead, for an appropriate substitution `rho`.
{-# SPECIALIZE unsafeEscapeContext :: Int -> TCM a -> TCM a #-}
unsafeEscapeContext :: MonadTCM tcm => Int -> tcm a -> tcm a
unsafeEscapeContext n = unsafeModifyContext $ cxDrop n

{-# SPECIALIZE escapeContext :: Impossible -> Int -> TCM a -> TCM a #-}
-- | Delete the last @n@ bindings from the context. Any occurrences of
-- these variables are replaced with the given @err@.
escapeContext :: MonadAddContext m => Impossible -> Int -> m a -> m a
escapeContext err n = updateContext (strengthenS err n) $ cxDrop n

-- * Manipulating checkpoints --

{-# SPECIALIZE checkpoint :: Substitution -> TCM a -> TCM a #-}
-- | Add a new checkpoint. Do not use directly!
checkpoint
  :: (MonadDebug tcm, MonadTCM tcm, MonadFresh CheckpointId tcm, ReadTCState tcm)
  => Substitution -> tcm a -> tcm a
checkpoint sub k = do
  unlessDebugPrinting $ reportSLn "tc.cxt.checkpoint" 105 $ "New checkpoint {"
  old  <- viewTC eCurrentCheckpoint
  oldChkpts <- useTC stModuleCheckpoints
  chkpt <- fresh
  unlessDebugPrinting $ verboseS "tc.cxt.checkpoint" 105 $ do
    cxt <- getContextTelescope
    cps <- viewTC eCheckpoints
    let cps' = Map.insert chkpt IdS $ fmap (applySubst sub) cps
        prCps cps = vcat [ pshow c <+> ": " <+> pretty s | (c, s) <- Map.toList cps ]
    reportS "tc.cxt.checkpoint" 105 $ nest 2 $ vcat
      [ "old =" <+> pshow old
      , "new =" <+> pshow chkpt
      , "sub =" <+> pretty sub
      , "cxt =" <+> pretty cxt
      , "mods =" <+> pretty oldChkpts
      , "old substs =" <+> prCps cps
      , "new substs =" <?> prCps cps'
      ]
  x <- flip localTC k $ \ env -> env
    { envCurrentCheckpoint = chkpt
    , envCheckpoints       = Map.insert chkpt IdS $
                              fmap (applySubst sub) (envCheckpoints env)
    }
  unlessDebugPrinting $ verboseS "tc.cxt.checkpoint" 105 $ do
    newChkpts <- useTC stModuleCheckpoints
    reportS "tc.cxt.checkpoint" 105 $ nest 2 $
      "mods before unwind =" <+> pretty newChkpts

  -- Set the checkpoint for introduced modules to the old checkpoint when the
  -- new one goes out of scope. #2897: This isn't actually sound for modules
  -- created under refined parent parameters, but as long as those modules
  -- aren't named we shouldn't look at the checkpoint. The right thing to do
  -- would be to not store these modules in the checkpoint map, but todo..

  -- [HACK: Repairing module checkpoints after state resets]
  -- Ideally, we could just walk up the current module checkpoint stack
  -- until we hit the the @old@ checkpoint. This works in most cases, but breaks if
  -- @k@ resets the typechecking state to a state defined *before* the call to
  -- @checkpoint@: this can result in us discarding module checkpoints.
  --
  -- To prevent this, we walk up the current module checkpoint stack until
  -- we hit our previous checkpoint, and add any module checkpoints onto
  -- the checkpoint stack we had before we ran @k@.
  unwindModuleCheckpointsOnto old oldChkpts

  unlessDebugPrinting $ verboseS "tc.cxt.checkpoint" 105 $ do
    unwoundChkpts <- useTC stModuleCheckpoints
    reportS "tc.cxt.checkpoint" 105 $ nest 2 $
      "unwound mods =" <+> pretty unwoundChkpts

  unlessDebugPrinting $ reportSLn "tc.cxt.checkpoint" 105 "}"
  return x

-- | Add a module checkpoint for the provided @ModuleName@.
{-# SPECIALIZE setModuleCheckpoint :: ModuleName -> CheckpointId -> TCM () #-}
setModuleCheckpoint :: (MonadTCState m) => ModuleName -> CheckpointId -> m ()
setModuleCheckpoint mname newChkpt =
  modifyTCLens' stModuleCheckpoints \case
      (ModuleCheckpointsSection chkpts mnames chkpt) | chkpt == newChkpt ->
        ModuleCheckpointsSection chkpts (Set.insert mname mnames) chkpt
      chkpts -> ModuleCheckpointsSection chkpts (Set.singleton mname) newChkpt

-- | Set every module checkpoint in the checkpoint stack to the provided @CheckpointId@.
{-# SPECIALIZE setAllModuleCheckpoints :: CheckpointId -> TCM () #-}
setAllModuleCheckpoints :: (MonadTCState m) => CheckpointId -> m ()
setAllModuleCheckpoints chkpt =
  modifyTCLens' stModuleCheckpoints \case
    ModuleCheckpointsTop -> ModuleCheckpointsTop
    ModuleCheckpointsSection chkpts siblings _ -> setAll siblings chkpts
  where
    setAll :: Set ModuleName -> ModuleCheckpoints -> ModuleCheckpoints
    setAll acc ModuleCheckpointsTop = ModuleCheckpointsSection ModuleCheckpointsTop acc chkpt
    setAll acc (ModuleCheckpointsSection chkpts siblings _) = setAll (Set.union siblings acc) chkpts

-- | Unwind the current module checkpoint stack until we reach a target @CheckpointId@,
--   and place the checkpoints onto the provided @ModuleCheckpoints@ stack.
{-# SPECIALIZE unwindModuleCheckpointsOnto :: CheckpointId -> ModuleCheckpoints -> TCM () #-}
unwindModuleCheckpointsOnto :: (MonadTCState m) => CheckpointId -> ModuleCheckpoints -> m ()
unwindModuleCheckpointsOnto unwindTo oldChkpts =
  -- We know that the checkpoints in the stack are sorted,
  -- so we can do a preliminary check to see if there's
  -- any work to be done.
  modifyTCLens' stModuleCheckpoints \case
    ModuleCheckpointsSection chkpts siblings chkpt | unwindTo < chkpt -> unwind siblings chkpts
    _ -> oldChkpts
  where
    unwind :: Set ModuleName -> ModuleCheckpoints -> ModuleCheckpoints
    unwind acc ModuleCheckpointsTop =
      ModuleCheckpointsSection ModuleCheckpointsTop acc unwindTo
    unwind acc (ModuleCheckpointsSection chkpts siblings chkpt)
      | chkpt < unwindTo =
        -- If the unwind target isnt present in the stack, we add it
        -- ourselves.
        ModuleCheckpointsSection oldChkpts acc unwindTo
      | chkpt == unwindTo =
        -- Make sure to avoid adding duplicate entries into the unwind
        -- stack: this would break later unwinds!
        ModuleCheckpointsSection oldChkpts (Set.union siblings acc) chkpt
      | otherwise = unwind (Set.union siblings acc) chkpts

-- | Run a computation with no module checkpoints set.
withoutModuleCheckpoints :: (ReadTCState m) => m a -> m a
withoutModuleCheckpoints cont =
  locallyTCState stModuleCheckpoints (const ModuleCheckpointsTop) cont
{-# INLINE withoutModuleCheckpoints #-}

-- | Get the substitution from the context at a given checkpoint to the current context.
checkpointSubstitution :: MonadTCEnv tcm => CheckpointId -> tcm Substitution
checkpointSubstitution = maybe __IMPOSSIBLE__ return <=< checkpointSubstitution'

-- | Get the substitution from the context at a given checkpoint to the current context.
checkpointSubstitution' :: MonadTCEnv tcm => CheckpointId -> tcm (Maybe Substitution)
checkpointSubstitution' chkpt = viewTC (eCheckpoints . key chkpt)

-- | Get the @CheckpointId@ of a module name.
getModuleCheckpoint :: ModuleName -> ModuleCheckpoints -> Maybe CheckpointId
getModuleCheckpoint mname ModuleCheckpointsTop = Nothing
getModuleCheckpoint mname (ModuleCheckpointsSection chkpts siblings chkid)
  | Set.member mname siblings = Just chkid
  | otherwise = getModuleCheckpoint mname chkpts

-- | Get substitution @Γ ⊢ ρ : Γm@ where @Γ@ is the current context
--   and @Γm@ is the module parameter telescope of module @m@.
--
--   Returns @Nothing@ in case the we don't have a checkpoint for @m@.
getModuleParameterSub :: (MonadTCEnv m, ReadTCState m) => ModuleName -> m (Maybe Substitution)
getModuleParameterSub m = do
  chkpt <- getModuleCheckpoint m <$> useTC stModuleCheckpoints
  traverse checkpointSubstitution chkpt

-- * Adding to the context

class MonadTCEnv m => MonadAddContext m where
  -- | @addCtx x arg cont@ add a variable to the context.
  --
  --   Chooses an unused 'Name'.
  --
  --   Warning: Does not update module parameter substitution!
  addCtx :: Name -> Dom Type -> m a -> m a

  -- | Add a let bound variable to the context
  addLetBinding' ::
       IsAxiom   -- ^ Does this let binding come from a 'LetAxiom'?
    -> Origin -> Name -> Term -> Dom Type -> m a -> m a

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
    => IsAxiom -> Origin -> Name -> Term -> Dom Type -> m a -> m a
  addLetBinding' isAxiom o x u a = liftThrough $ addLetBinding' isAxiom o x u a

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

{-# INLINE defaultAddCtx #-}
-- | Default implementation of addCtx in terms of updateContext
defaultAddCtx :: MonadAddContext m => Name -> Dom Type -> m a -> m a
defaultAddCtx x a ret =
  updateContext (raiseS 1) (CxExtendVar x a) ret

withFreshName_ :: (MonadAddContext m) => ArgName -> (Name -> m a) -> m a
withFreshName_ = withFreshName noRange

instance MonadAddContext m => MonadAddContext (ChangeT m)
instance MonadAddContext m => MonadAddContext (ExceptT e m)
instance MonadAddContext m => MonadAddContext (IdentityT m)
instance MonadAddContext m => MonadAddContext (MaybeT m)
instance MonadAddContext m => MonadAddContext (ReaderT r m)
instance MonadAddContext m => MonadAddContext (StateT r m)
instance (Monoid w, MonadAddContext m) => MonadAddContext (WriterT w m)
deriving instance MonadAddContext m => MonadAddContext (BlockT m)

instance MonadAddContext m => MonadAddContext (ListT m) where
  addCtx x a             = liftListT $ addCtx x a
  addLetBinding' isAxiom o x u a = liftListT $ addLetBinding' isAxiom o x u a
  updateContext sub f    = liftListT $ updateContext sub f
  withFreshName r x cont = ListT $ withFreshName r x $ runListT . cont

-- | Run the given TCM action, and register the given variable as
--   being shadowed by all the names with the same root that are added
--   to the context during this TCM action.
withShadowingNameTCM :: Name -> TCM b -> TCM b
withShadowingNameTCM x f = do
  reportS "tc.cxt.shadowing" 80 $ "registered" <+> pretty x <+> "for shadowing"
  when (isInScope x == InScope) $ tellUsedName x
  (result , useds) <- listenUsedNames f
  reportSLn "tc.cxt.shadowing" 90 $ "all used names: " ++ show useds
  tellShadowing x useds
  return result

    where
      listenUsedNames f = do
        origUsedNames <- useTC stUsedNames
        setTCLens stUsedNames Map.empty
        result <- f
        newUsedNames <- useTC stUsedNames
        setTCLens stUsedNames $ Map.unionWith (<>) origUsedNames newUsedNames
        return (result , newUsedNames)

      tellUsedName x = do
        let concreteX = nameConcrete x
            rawX      = nameToRawName concreteX
            rootX     = nameRoot concreteX
        modifyTCLens (stUsedNames . key rootX) $
          Just . (Set1.insertSet rawX) . Set1.toSet'

      tellShadowing x useds = case Map.lookup (nameRoot $ nameConcrete x) useds of
        Just shadows -> do
          reportS "tc.cxt.shadowing" 80 $
            "names shadowing" <+> pretty x <+> ": " <+>
            prettyList_ (map pretty $ toList shadows)
          modifyTCLens stShadowingNames $ Map.insertWith (<>) x shadows
        Nothing      -> return ()

instance MonadAddContext TCM where
  addCtx x a ret = applyUnless (isNoName x) (withShadowingNameTCM x) $
    defaultAddCtx x a ret

  addLetBinding' isAxiom o x u a ret = applyUnless (isNoName x) (withShadowingNameTCM x) $
    defaultAddLetBinding' isAxiom o x u a ret

  updateContext sub f = unsafeModifyContext f . checkpoint sub

  withFreshName r x m = freshName r x >>= m

addRecordNameContext
  :: (MonadAddContext m, MonadFresh NameId m)
  => Dom Type -> m b -> m b
addRecordNameContext dom ret = do
  x <- setNotInScope <$> freshRecordName
  addCtx x dom ret

-- | Various specializations of @addCtx@.
class AddContext b where
  addContext :: (MonadAddContext m) => b -> m a -> m a
  contextSize :: b -> Nat

-- | Wrapper to tell 'addContext' not to mark names as
--   'NotInScope'. Used when adding a user-provided, but already type
--   checked, telescope to the context.
newtype KeepNames a = KeepNames a

instance {-# OVERLAPPABLE #-} AddContext a => AddContext [a] where
  addContext = flip (foldr addContext); {-# INLINABLE addContext #-}
  contextSize = sum . map contextSize

instance AddContext Context where
  addContext = flip (foldl $ flip addContext); {-# INLINABLE addContext #-}
  contextSize = sum . map contextSize . cxEntries

instance AddContext ContextEntry where
  addContext (CtxVar x a) = addCtx x a
  {-# INLINE addContext #-}
  contextSize _ = 1

instance AddContext (Name, Dom Type) where
  addContext = uncurry addCtx; {-# INLINE addContext #-}
  contextSize _ = 1
{-# SPECIALIZE addContext :: (Name, Dom Type) -> TCM a -> TCM a #-}

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

instance AddContext ([Dom Name], Type) where
  addContext ([], _)     = id
  addContext (x : xs, t) = addContext (x :| xs, t)
  contextSize (xs, _) = length xs

instance AddContext (List1 (Dom Name), Type) where
  addContext (x :| xs, t) =
    addContext (unDom x, x $> t) .
    addContext (xs, raise 1 t)
  contextSize (xs, _) = length xs

instance AddContext (String, Dom Type) where
  addContext (s, dom) ret =
    withFreshName noRange s $ \x -> addCtx (setNotInScope x) dom ret
  contextSize _ = 1
{-# SPECIALIZE addContext :: (String, Dom Type) -> TCM a -> TCM a #-}

instance AddContext (Text, Dom Type) where
  addContext (s, dom) ret = addContext (T.unpack s, dom) ret
  contextSize _ = 1
{-# SPECIALIZE addContext :: (Text, Dom Type) -> TCM a -> TCM a #-}

instance AddContext (KeepNames String, Dom Type) where
  addContext (KeepNames s, dom) ret =
    withFreshName noRange s $ \ x -> addCtx x dom ret
  contextSize _ = 1
{-# SPECIALIZE addContext :: (KeepNames String, Dom Type) -> TCM a -> TCM a #-}

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
{-# SPECIALIZE addContext :: KeepNames Telescope -> TCM a -> TCM a #-}

instance AddContext Telescope where
  addContext tel ret = loop tel where
    loop EmptyTel          = ret
    loop (ExtendTel t tel) = underAbstraction' id t tel loop
  contextSize = size
{-# SPECIALIZE addContext :: Telescope -> TCM a -> TCM a #-}

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
  :: (Subst a, MonadAddContext m)
  => Dom Type -> (a -> m b) -> Abs a -> m (Abs b)
mapAbstraction dom f x = (x $>) <$> underAbstraction dom x f

mapAbstraction_
  :: (Subst a, MonadAddContext m)
  => (a -> m b) -> Abs a -> m (Abs b)
mapAbstraction_ = mapAbstraction __DUMMY_DOM__

{-# SPECIALIZE getLetBindings :: TCM [(Name, LetBinding)] #-}
getLetBindings :: MonadTCEnv tcm => tcm [(Name, LetBinding)]
getLetBindings = do
  bs <- asksTC envLetBindings
  forM (Map.toList bs) $ \ (n, o) -> (,) n <$> getOpen o

-- | Add a let bound variable.
{-# SPECIALIZE defaultAddLetBinding' :: IsAxiom -> Origin -> Name -> Term -> Dom Type -> TCM a -> TCM a #-}
defaultAddLetBinding' :: (ReadTCState m, MonadTCEnv m)
  => IsAxiom   -- ^ Does this let binding come from a 'LetAxiom'?
  -> Origin -> Name -> Term -> Dom Type -> m a -> m a
defaultAddLetBinding' isAxiom o x v t ret = do
    vt <- makeOpen $ LetBinding isAxiom o v t
    flip localTC ret $ \e -> e { envLetBindings = Map.insert x vt $ envLetBindings e }

-- | Add a let bound variable.
{-# SPECIALIZE addLetBinding :: ArgInfo -> Origin -> Name -> Term -> Type -> TCM a -> TCM a #-}
addLetBinding :: MonadAddContext m => ArgInfo -> Origin -> Name -> Term -> Type -> m a -> m a
addLetBinding info o x v t0 ret = addLetBinding' NoAxiom o x v (defaultArgDom info t0) ret

-- | Add a let bound variable without a definition.
{-# SPECIALIZE addLetAxiom :: ArgInfo -> Origin -> Name -> Term -> Type -> TCM a -> TCM a #-}
addLetAxiom :: MonadAddContext m => ArgInfo -> Origin -> Name -> Term -> Type -> m a -> m a
addLetAxiom info o x v t0 ret = addLetBinding' YesAxiom o x v (defaultArgDom info t0) ret

{-# SPECIALIZE removeLetBinding :: Name -> TCM a -> TCM a #-}
-- | Remove a let bound variable.
removeLetBinding :: MonadTCEnv m => Name -> m a -> m a
removeLetBinding x = localTC $ \ e -> e { envLetBindings = Map.delete x (envLetBindings e) }

{-# SPECIALIZE removeLetBindingsFrom :: Name -> TCM a -> TCM a #-}
-- | Remove a let bound variable and all let bindings introduced after it. For instance before
--   printing its body to avoid folding the binding itself, or using bindings defined later.
--   Relies on the invariant that names introduced later are sorted after earlier names.
removeLetBindingsFrom :: MonadTCEnv m => Name -> m a -> m a
removeLetBindingsFrom x = localTC $ \ e -> e { envLetBindings = fst $ Map.split x (envLetBindings e) }

-- * Querying the context

-- | Get the current context.
{-# SPECIALIZE getContext :: TCM Context #-}
getContext :: MonadTCEnv m => m Context
getContext = asksTC envContext

-- | Get the size of the current context.
{-# SPECIALIZE getContextSize :: TCM Nat #-}
getContextSize :: (MonadTCEnv m) => m Nat
getContextSize = size <$> getContext

{-# SPECIALIZE getContextVars :: TCM [(Int, Dom Name)] #-}
getContextVars :: (MonadTCEnv m) => m [(Int, Dom Name)]
getContextVars = contextVars <$> getContext

{-# SPECIALIZE getContextVars' :: TCM [(Int, Dom Name)] #-}
getContextVars' :: (MonadTCEnv m) => m [(Int, Dom Name)]
getContextVars' = contextVars' <$> getContext

contextVars :: Context -> [(Int, Dom Name)]
contextVars = reverse . contextVars'

contextVars' :: Context -> [(Int, Dom Name)]
contextVars' = cxWithIndex mkVar
  where
    mkVar i (CtxVar x a) = (i, a $> x)

-- | Generate @[var (n - 1), ..., var 0]@ for all bound variables in the context.
{-# SPECIALIZE getContextArgs :: TCM Args #-}
getContextArgs :: (MonadTCEnv m) => m Args
getContextArgs = contextArgs <$> getContext

contextArgs :: Context -> Args
contextArgs = map (\(i,x) -> var i <$ argFromDom x) . contextVars

-- | Generate @[var (n - 1), ..., var 0]@ for all declarations in the context.
{-# SPECIALIZE getContextTerms :: TCM [Term] #-}
getContextTerms :: (MonadTCEnv m) => m [Term]
getContextTerms = map unArg <$> getContextArgs

contextTerms :: Context -> [Term]
contextTerms = map unArg . contextArgs

-- | Get the current context as a 'Telescope'.
{-# SPECIALIZE getContextTelescope :: TCM Telescope #-}
getContextTelescope :: (MonadTCEnv m) => m Telescope
getContextTelescope = contextToTel <$> getContext

contextToTel :: Context -> Telescope
contextToTel = go EmptyTel
  where
    go tel CxEmpty               = tel
    go tel (CxExtendVar x a ctx) = go (ExtendTel a $ Abs (nameToArgName x) tel) ctx

-- | Get the names of all declarations in the context.
{-# SPECIALIZE getContextNames :: TCM [Name] #-}
getContextNames :: (MonadTCEnv m) => m [Name]
getContextNames = contextNames <$> getContext

{-# SPECIALIZE getContextNames' :: TCM [Name] #-}
getContextNames' :: (MonadTCEnv m) => m [Name]
getContextNames' = contextNames' <$> getContext

contextNames :: Context -> [Name]
contextNames = map (unDom . snd) . contextVars

contextNames' :: Context -> [Name]
contextNames' = map (unDom . snd) . contextVars'

-- | get type of bound variable (i.e. deBruijn index)
--
lookupBV_ :: Nat -> Context -> Maybe ContextEntry
lookupBV_ n ctx = raise (n + 1) <$> cxLookup n ctx

{-# SPECIALIZE lookupBV' :: Nat -> TCM (Maybe ContextEntry) #-}
lookupBV' :: MonadTCEnv m => Nat -> m (Maybe ContextEntry)
lookupBV' n = lookupBV_ n <$> getContext

{-# SPECIALIZE lookupBV :: Nat -> TCM ContextEntry #-}
lookupBV :: (MonadDebug m, MonadTCEnv m) => Nat -> m ContextEntry
lookupBV n = do
  let failure = do
        ctx <- getContext
        __IMPOSSIBLE_VERBOSE__ $ unwords
          [ "de Bruijn index out of scope:", show n
          , "in context", prettyShow $ map ctxEntryName $ cxEntries ctx
          ]
  caseMaybeM (lookupBV' n) failure return

ctxEntryName :: ContextEntry -> Name
ctxEntryName (CtxVar x _) = x

ctxEntryDom :: ContextEntry -> Dom Type
ctxEntryDom (CtxVar _ a) = a

ctxEntryType :: ContextEntry -> Type
ctxEntryType = unDom . ctxEntryDom

{-# SPECIALIZE domOfBV :: Nat -> TCM (Dom Type) #-}
domOfBV :: (MonadDebug m, MonadTCEnv m) => Nat -> m (Dom Type)
domOfBV n = ctxEntryDom <$> lookupBV n

{-# SPECIALIZE typeOfBV :: Nat -> TCM Type #-}
typeOfBV :: (MonadDebug m, MonadTCEnv m) => Nat -> m Type
typeOfBV i = unDom <$> domOfBV i

{-# SPECIALIZE nameOfBV' :: Nat -> TCM (Maybe Name) #-}
nameOfBV' :: (MonadTCEnv m) => Nat -> m (Maybe Name)
nameOfBV' n = fmap ctxEntryName <$> lookupBV' n

{-# SPECIALIZE nameOfBV :: Nat -> TCM Name #-}
nameOfBV :: (MonadDebug m, MonadTCEnv m) => Nat -> m Name
nameOfBV n = ctxEntryName <$> lookupBV n

-- | Get the term corresponding to a named variable. If it is a lambda bound
--   variable the deBruijn index is returned and if it is a let bound variable
--   its definition is returned.
{-# SPECIALIZE getVarInfo :: Name -> TCM (Term, Dom Type) #-}
getVarInfo :: (MonadDebug m, MonadFail m, MonadTCEnv m) => Name -> m (Term, Dom Type)
getVarInfo x =
    do  ctx <- getContextVars'
        def <- asksTC envLetBindings
        case List.findIndex ((== x) . unDom . snd) ctx of
            Just n -> do
                t <- domOfBV n
                return (var n, t)
            _       ->
                case Map.lookup x def of
                    Just vt -> do
                      LetBinding _isAxiom _origin v t <- getOpen vt
                      return (v, t)
                    _ -> fail $ unwords
                      [ "unbound variable"
                      , prettyShow $ nameConcrete x
                      , "(id: " ++ prettyShow (nameId x) ++ ")"
                      ]
                      -- Andreas, 2026-01-20, issue #8325
                      -- This 'fail' is apparently not impossible;
                      -- it is apparently caught during a "refine".
                      -- TODO: It would be worthwhile investigating who wants to access
                      -- an out-of-scope variable.
