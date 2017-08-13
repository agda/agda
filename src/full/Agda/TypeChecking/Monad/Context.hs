{-# LANGUAGE CPP               #-}

#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

module Agda.TypeChecking.Monad.Context where

import Control.Applicative
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
import Agda.Utils.Pretty
import Agda.Utils.Size

-- * Modifying the context

-- | Modify the 'ctxEntry' field of a 'ContextEntry'.
modifyContextEntry :: (Dom (Name, Type) -> Dom (Name, Type)) -> ContextEntry -> ContextEntry
modifyContextEntry f ce = ce { ctxEntry = f (ctxEntry ce) }

-- | Modify all 'ContextEntry's.
modifyContextEntries :: (Dom (Name, Type) -> Dom (Name, Type)) -> Context -> Context
modifyContextEntries f = map (modifyContextEntry f)

-- | Modify a 'Context' in a computation.
{-# SPECIALIZE modifyContext :: (Context -> Context) -> TCM a -> TCM a #-}
modifyContext :: MonadTCM tcm => (Context -> Context) -> tcm a -> tcm a
modifyContext f = local $ \e -> e { envContext = f $ envContext e }

{-# SPECIALIZE mkContextEntry :: Dom (Name, Type) -> TCM ContextEntry #-}
mkContextEntry :: MonadTCM tcm => Dom (Name, Type) -> tcm ContextEntry
mkContextEntry x = do
  i <- fresh
  return $ Ctx i x

-- | Change to top (=empty) context.
--
--   TODO: currently, this makes the @ModuleParamDict@ ill-formed!
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
--   TODO: currently, this makes the @ModuleParamDict@ ill-formed!
{-# SPECIALIZE escapeContext :: Int -> TCM a -> TCM a #-}
escapeContext :: MonadTCM tcm => Int -> tcm a -> tcm a
escapeContext n = modifyContext $ drop n

-- * Manipulating module parameters --

-- | Locally set module parameters for a computation.

withModuleParameters :: ModuleParamDict -> TCM a -> TCM a
withModuleParameters mp ret = do
  old <- use stModuleParameters
  stModuleParameters .= mp
  x <- ret
  stModuleParameters .= old
  return x

-- | Apply a substitution to all module parameters.

updateModuleParameters :: (MonadTCM tcm, MonadDebug tcm)
                       => Substitution -> tcm a -> tcm a
updateModuleParameters sub ret = do
  pm <- use stModuleParameters
  let showMP pref mps = List.intercalate "\n" $
        [ p ++ show m ++ " : " ++ show (mpSubstitution mp)
        | (p, (m, mp)) <- zip (pref : repeat (map (const ' ') pref))
                              (Map.toList mps)
        ]
  verboseS "tc.cxt.param" 90 $ do
    cxt <- reverse <$> getContext
    reportSLn "tc.cxt.param" 90 $ unlines $
      [ "updatingModuleParameters"
      , "  sub = " ++ show sub
      , "  cxt (last added last in list) = " ++ unwords (map (show . fst . unDom) cxt)
      , showMP "  old = " pm
      ]
  let pm' = applySubst sub pm
  reportSLn "tc.cxt.param" 90 $ showMP "  new = " pm'
  stModuleParameters .= pm'
  x <- ret              -- We need to keep introduced modules around
  pm1 <- use stModuleParameters
  let pm'' = Map.union pm (defaultModuleParameters <$ Map.difference pm1 pm)
  stModuleParameters .= pm''
  reportSLn "tc.cxt.param" 90 $ showMP "  restored = " pm''
  return x

-- | Since the @ModuleParamDict@ is relative to the current context,
--   this function should be called everytime the context is extended.
--
weakenModuleParameters :: (MonadTCM tcm, MonadDebug tcm)
                       => Nat -> tcm a -> tcm a
weakenModuleParameters n = updateModuleParameters (raiseS n)

-- | Get substitution @Γ ⊢ ρ : Γm@ where @Γ@ is the current context
--   and @Γm@ is the module parameter telescope of module @m@.
--
--   In case the current 'ModuleParamDict' does not know @m@,
--   we return the identity substitution.
--   This is ok for instance if we are outside module @m@
--   (in which case we have to supply all module parameters to any
--   symbol defined within @m@ we want to refer).
getModuleParameterSub :: (Functor m, ReadTCState m) => ModuleName -> m Substitution
getModuleParameterSub m = do
  r <- (^. stModuleParameters) <$> getTCState
  case Map.lookup m r of
    Nothing -> return IdS
    Just mp -> return $ mpSubstitution mp


-- * Adding to the context

-- | @addCtx x arg cont@ add a variable to the context.
--
--   Chooses an unused 'Name'.
--
--   Warning: Does not update module parameter substitution!
{-# SPECIALIZE addCtx :: Name -> Dom Type -> TCM a -> TCM a #-}
addCtx :: MonadTCM tcm => Name -> Dom Type -> tcm a -> tcm a
addCtx x a ret = do
  ce <- mkContextEntry $ (x,) <$> a
  modifyContext (ce :) ret
      -- let-bindings keep track of own their context

-- | Pick a concrete name that doesn't shadow anything in the context.
unshadowName :: MonadTCM tcm => Name -> tcm Name
unshadowName x = do
  ctx <- map (nameConcrete . fst . unDom) <$> getContext
  return $ head $ filter (notTaken ctx) $ iterate nextName x
  where
    notTaken xs x = isNoName x || nameConcrete x `notElem` xs

-- | Various specializations of @addCtx@.
{-# SPECIALIZE addContext :: b -> TCM a -> TCM a #-}
class AddContext b where
  addContext  :: MonadTCM tcm => b -> tcm a -> tcm a
  contextSize :: b -> Nat

-- | Since the module parameter substitution is relative to
--   the current context, we need to weaken it when we
--   extend the context.  This function takes care of that.
--
addContext' :: (MonadTCM tcm, MonadDebug tcm, AddContext b)
            => b -> tcm a -> tcm a
addContext' cxt = addContext cxt . weakenModuleParameters (contextSize cxt)

-- | Wrapper to tell 'addContext' not to 'unshadowName's. Used when adding a
--   user-provided, but already type checked, telescope to the context.
newtype KeepNames a = KeepNames a

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPABLE #-} AddContext a => AddContext [a] where
#else
instance AddContext a => AddContext [a] where
#endif
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
  addContext x = addContext (x, dummyDom)
  contextSize _ = 1

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPING #-} AddContext String where
#else
instance AddContext String where
#endif
  addContext s = addContext (s, dummyDom)
  contextSize _ = 1

instance AddContext (KeepNames Telescope) where
  addContext (KeepNames tel) ret = loop tel where
    loop EmptyTel          = ret
    loop (ExtendTel t tel) = underAbstraction' KeepNames t tel loop
  contextSize (KeepNames tel) = size tel

instance AddContext Telescope where
  addContext tel ret = loop tel where
    loop EmptyTel          = ret
    loop (ExtendTel t tel) = underAbstraction t tel loop
  contextSize = size

-- | Context entries without a type have this dummy type.
dummyDom :: Dom Type
dummyDom = defaultDom typeDontCare

-- | Go under an abstraction.
{-# SPECIALIZE underAbstraction :: Subst t a => Dom Type -> Abs a -> (a -> TCM b) -> TCM b #-}
underAbstraction :: (Subst t a, MonadTCM tcm) => Dom Type -> Abs a -> (a -> tcm b) -> tcm b
underAbstraction = underAbstraction' id

underAbstraction' :: (Subst t a, MonadTCM tcm, AddContext (name, Dom Type)) =>
                     (String -> name) -> Dom Type -> Abs a -> (a -> tcm b) -> tcm b
underAbstraction' _ _ (NoAbs _ v) k = k v
underAbstraction' wrap t a        k = addContext (wrap $ realName $ absName a, t) $ k $ absBody a
  where
    realName s = if isNoName s then "x" else argNameToString s

-- | Go under an abstract without worrying about the type to add to the context.
{-# SPECIALIZE underAbstraction_ :: Subst t a => Abs a -> (a -> TCM b) -> TCM b #-}
underAbstraction_ :: (Subst t a, MonadTCM tcm) => Abs a -> (a -> tcm b) -> tcm b
underAbstraction_ = underAbstraction dummyDom

-- | Add a let bound variable.
{-# SPECIALIZE addLetBinding :: ArgInfo -> Name -> Term -> Type -> TCM a -> TCM a #-}
addLetBinding :: MonadTCM tcm => ArgInfo -> Name -> Term -> Type -> tcm a -> tcm a
addLetBinding info x v t0 ret = do
    let t = Dom info t0
    vt <- liftTCM $ makeOpen (v, t)
    flip local ret $ \e -> e { envLetBindings = Map.insert x vt $ envLetBindings e }


-- * Querying the context

-- | Get the current context.
{-# SPECIALIZE getContext :: TCM [Dom (Name, Type)] #-}
getContext :: MonadReader TCEnv m => m [Dom (Name, Type)]
getContext = asks $ map ctxEntry . envContext

-- | Get the size of the current context.
{-# SPECIALIZE getContextSize :: TCM Nat #-}
getContextSize :: (Applicative m, MonadReader TCEnv m) => m Nat
getContextSize = length <$> asks envContext

-- | Generate @[var (n - 1), ..., var 0]@ for all declarations in the context.
{-# SPECIALIZE getContextArgs :: TCM Args #-}
getContextArgs :: (Applicative m, MonadReader TCEnv m) => m Args
getContextArgs = reverse . zipWith mkArg [0..] <$> getContext
  where mkArg i (Dom info _) = Arg info $ var i

-- | Generate @[var (n - 1), ..., var 0]@ for all declarations in the context.
{-# SPECIALIZE getContextTerms :: TCM [Term] #-}
getContextTerms :: (Applicative m, MonadReader TCEnv m) => m [Term]
getContextTerms = map var . downFrom <$> getContextSize

-- | Get the current context as a 'Telescope'.
{-# SPECIALIZE getContextTelescope :: TCM Telescope #-}
getContextTelescope :: (Applicative m, MonadReader TCEnv m) => m Telescope
getContextTelescope = telFromList' nameToArgName . reverse <$> getContext

-- | Check if we are in a compatible context, i.e. an extension of the given context.
{-# SPECIALIZE getContextId :: TCM [CtxId] #-}
getContextId :: MonadReader TCEnv m => m [CtxId]
getContextId = asks $ map ctxId . envContext

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
getVarInfo
#if __GLASGOW_HASKELL__ <= 708
  :: (Applicative m, MonadReader TCEnv m)
#else
  :: MonadReader TCEnv m
#endif
  => Name -> m (Term, Dom Type)
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
                    _       -> fail $ "unbound variable " ++ prettyShow (nameConcrete x)
