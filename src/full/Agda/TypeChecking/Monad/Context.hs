{-# LANGUAGE TupleSections,
      FlexibleInstances, TypeSynonymInstances #-}

module Agda.TypeChecking.Monad.Context where

import Control.Monad.Reader

import Data.List hiding (sort)
import qualified Data.Map as Map

import Agda.Syntax.Concrete.Name (isNoName)
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common hiding (Arg, Dom, NamedArg, ArgInfo)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Internal
import Agda.Syntax.Scope.Monad (getLocalVars, setLocalVars)

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Open

import Agda.Utils.List ((!!!), downFrom)
import Agda.Utils.Monad
import Agda.Utils.Fresh

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

-- | Change the context.
{-# SPECIALIZE inContext :: [Dom (Name, Type)] -> TCM a -> TCM a #-}
inContext :: MonadTCM tcm => [Dom (Name, Type)] -> tcm a -> tcm a
inContext xs ret = do
  ctx <- mapM mkContextEntry xs
  modifyContext (const ctx) ret

-- | Change to top (=empty) context.
{-# SPECIALIZE inTopContext :: TCM a -> TCM a #-}
inTopContext :: MonadTCM tcm => tcm a -> tcm a
inTopContext cont = do
  locals <- liftTCM $ getLocalVars
  liftTCM $ setLocalVars []
  a <- modifyContext (const []) cont
  liftTCM $ setLocalVars locals
  return a

-- | Delete the last @n@ bindings from the context.
{-# SPECIALIZE escapeContext :: Int -> TCM a -> TCM a #-}
escapeContext :: MonadTCM tcm => Int -> tcm a -> tcm a
escapeContext n = modifyContext $ drop n

-- * Adding to the context

-- | @addCtx x arg cont@ add a variable to the context.
--
--   Chooses an unused 'Name'.
{-# SPECIALIZE addCtx :: Name -> Dom Type -> TCM a -> TCM a #-}
addCtx :: MonadTCM tcm => Name -> Dom Type -> tcm a -> tcm a
addCtx x a ret = do
  ctx <- map (nameConcrete . fst . unDom) <$> getContext
  let x' = head $ filter (notTaken ctx) $ iterate nextName x
  ce <- mkContextEntry $ (x',) <$> a
  modifyContext (ce :) ret
      -- let-bindings keep track of own their context
  where
    notTaken xs x = isNoName (nameConcrete x) || nameConcrete x `notElem` xs

-- | Various specializations of @addCtx@.
{-# SPECIALIZE addContext :: b -> TCM a -> TCM a #-}
class AddContext b where
  addContext :: MonadTCM tcm => b -> tcm a -> tcm a

instance AddContext a => AddContext [a] where
  addContext = flip (foldr addContext)

instance AddContext (Name, Dom Type) where
  addContext = uncurry addCtx

instance AddContext (Dom (Name, Type)) where
  addContext dom = addCtx (fst $ unDom dom) (snd <$> dom)

instance AddContext ([Name], Dom Type) where
  addContext (xs, dom) = addContext (bindsToTel' id xs dom)

instance AddContext (String, Dom Type) where
  addContext (s, dom) ret = do
    x <- freshName_ s
    addCtx x dom ret

instance AddContext Name where
  addContext x = addContext (x, dummyDom)

instance AddContext String where
  addContext s = addContext (s, dummyDom)

instance AddContext Telescope where
  addContext tel ret = loop tel where
    loop EmptyTel          = ret
    loop (ExtendTel t tel) = underAbstraction t tel loop

{-
-- | N-ary variant of @addCtx@.
{-# SPECIALIZE addContext :: [Dom (Name, Type)] -> TCM a -> TCM a #-}
addContext :: MonadTCM tcm => [Dom (Name, Type)] -> tcm a -> tcm a
addContext ctx m =
  foldr (\arg -> addCtx (fst $ unDom arg) (snd <$> arg)) m ctx
-}

-- | add a bunch of variables with the same type to the context
{-# SPECIALIZE addCtxs :: [Name] -> Dom Type -> TCM a -> TCM a #-}
addCtxs :: MonadTCM tcm => [Name] -> Dom Type -> tcm a -> tcm a
addCtxs []     _ k = k
addCtxs (x:xs) t k = addCtx x t $ addCtxs xs (raise 1 t) k

-- | Turns the string into a name and adds it to the context.
{-# SPECIALIZE addCtxString :: String -> Dom Type -> TCM a -> TCM a #-}
addCtxString :: MonadTCM tcm => String -> Dom Type -> tcm a -> tcm a
addCtxString s a m = do
  x <- freshName_ s
  addCtx x a m

-- | Turns the string into a name and adds it to the context, with dummy type.
{-# SPECIALIZE addCtxString_ :: String -> TCM a -> TCM a #-}
addCtxString_ :: MonadTCM tcm => String -> tcm a -> tcm a
addCtxString_ s = addCtxString s dummyDom

{-# SPECIALIZE addCtxStrings_ :: [String] -> TCM a -> TCM a #-}
addCtxStrings_ :: MonadTCM tcm => [String] -> tcm a -> tcm a
addCtxStrings_ = flip (foldr addCtxString_)

-- | Context entries without a type have this dummy type.
dummyDom :: Dom Type
dummyDom = Common.Dom defaultArgInfo $ El Prop $ Sort Prop

-- | Go under an abstraction.
{-# SPECIALIZE underAbstraction :: Subst a => Dom Type -> Abs a -> (a -> TCM b) -> TCM b #-}
underAbstraction :: (Subst a, MonadTCM tcm) => Dom Type -> Abs a -> (a -> tcm b) -> tcm b
underAbstraction _ (NoAbs _ v) k = k v
underAbstraction t a           k = do
    x <- freshName_ $ realName $ absName a
    addCtx x t $ k $ absBody a
  where
    realName "_" = "x"
    realName s   = s

-- | Go under an abstract without worrying about the type to add to the context.
{-# SPECIALIZE underAbstraction_ :: Subst a => Abs a -> (a -> TCM b) -> TCM b #-}
underAbstraction_ :: (Subst a, MonadTCM tcm) => Abs a -> (a -> tcm b) -> tcm b
underAbstraction_ = underAbstraction dummyDom

-- | Add a telescope to the context.
{-# SPECIALIZE addCtxTel :: Telescope -> TCM a -> TCM a #-}
addCtxTel :: MonadTCM tcm => Telescope -> tcm a -> tcm a
addCtxTel tel ret = loop tel where
  loop EmptyTel          = ret
  loop (ExtendTel t tel) = underAbstraction t tel loop

-- | Add a let bound variable
{-# SPECIALIZE addLetBinding :: ArgInfo -> Name -> Term -> Type -> TCM a -> TCM a #-}
addLetBinding :: MonadTCM tcm => ArgInfo -> Name -> Term -> Type -> tcm a -> tcm a
addLetBinding info x v t0 ret = do
    let t = Common.Dom (setHiding NotHidden info) t0
    vt <- liftTCM $ makeOpen (v, t)
    flip local ret $ \e -> e { envLetBindings = Map.insert x vt $ envLetBindings e }


-- * Querying the context

-- | Get the current context.
{-# SPECIALIZE getContext :: TCM [Dom (Name, Type)] #-}
getContext :: MonadTCM tcm => tcm [Dom (Name, Type)]
getContext = asks $ map ctxEntry . envContext

-- | Get the size of the current context.
{-# SPECIALIZE getContextSize :: TCM Nat #-}
getContextSize :: MonadTCM tcm => tcm Nat
getContextSize = genericLength <$> asks envContext

-- | Generate @[var (n - 1), ..., var 0]@ for all declarations in the context.
{-# SPECIALIZE getContextArgs :: TCM Args #-}
getContextArgs :: MonadTCM tcm => tcm Args
getContextArgs = reverse . zipWith mkArg [0..] <$> getContext
  where mkArg i (Common.Dom info _) = Common.Arg info $ var i

{-# SPECIALIZE getContextTerms :: TCM [Term] #-}
getContextTerms :: MonadTCM tcm => tcm [Term]
getContextTerms = map var . downFrom <$> getContextSize

-- | Get the current context as a 'Telescope'.
{-# SPECIALIZE getContextTelescope :: TCM Telescope #-}
getContextTelescope :: MonadTCM tcm => tcm Telescope
getContextTelescope = telFromList' show . reverse <$> getContext

-- | Check if we are in a compatible context, i.e. an extension of the given context.
{-# SPECIALIZE getContextId :: TCM [CtxId] #-}
getContextId :: MonadTCM tcm => tcm [CtxId]
getContextId = asks $ map ctxId . envContext

-- | get type of bound variable (i.e. deBruijn index)
--
{-# SPECIALIZE lookupBV :: Nat -> TCM (Dom (Name, Type)) #-}
lookupBV :: MonadTCM tcm => Nat -> tcm (Dom (Name, Type))
lookupBV n = do
  ctx <- getContext
  let failure = fail $ "deBruijn index out of scope: " ++ show n ++
                       " in context " ++ show (map (fst . unDom) ctx)
  maybe failure (return . fmap (raise $ n + 1)) $ ctx !!! n

{-# SPECIALIZE typeOfBV' :: Nat -> TCM (Dom Type) #-}
typeOfBV' :: MonadTCM tcm => Nat -> tcm (Dom Type)
typeOfBV' n = fmap snd <$> lookupBV n

{-# SPECIALIZE typeOfBV :: Nat -> TCM Type #-}
typeOfBV :: MonadTCM tcm => Nat -> tcm Type
typeOfBV i = unDom <$> typeOfBV' i

{-# SPECIALIZE nameOfBV :: Nat -> TCM Name #-}
nameOfBV :: MonadTCM tcm => Nat -> tcm Name
nameOfBV n = fst . unDom <$> lookupBV n

-- | Get the term corresponding to a named variable. If it is a lambda bound
--   variable the deBruijn index is returned and if it is a let bound variable
--   its definition is returned.
{-# SPECIALIZE getVarInfo :: Name -> TCM (Term, Dom Type) #-}
getVarInfo :: MonadTCM tcm => Name -> tcm (Term, Dom Type)
getVarInfo x =
    do	ctx <- getContext
	def <- asks envLetBindings
	case findIndex ((==x) . fst . unDom) ctx of
	    Just n -> do
                t <- typeOfBV' n
                return (var n, t)
	    _	    ->
		case Map.lookup x def of
		    Just vt -> liftTCM $ getOpen vt
		    _	    -> fail $ "unbound variable " ++ show x
