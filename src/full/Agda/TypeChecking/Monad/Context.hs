{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Context where

import Control.Monad.Reader
import Data.List hiding (sort)
import qualified Data.Map as Map

import Agda.Syntax.Concrete.Name (isNoName)
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common hiding (Arg, Dom, NamedArg, ArgInfo)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Internal
import Agda.Syntax.Scope.Base
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Open

import Agda.Utils.Monad
import Agda.Utils.Fresh

#include "../../undefined.h"
import Agda.Utils.Impossible

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
inTopContext = modifyContext $ const []

-- | Delete the last @n@ bindings from the context.
{-# SPECIALIZE escapeContext :: Int -> TCM a -> TCM a #-}
escapeContext :: MonadTCM tcm => Int -> tcm a -> tcm a
escapeContext n = modifyContext $ drop n

-- | Deprecated.
{-# SPECIALIZE escapeContextToTopLevel :: TCM a -> TCM a #-}
escapeContextToTopLevel :: MonadTCM tcm => tcm a -> tcm a
escapeContextToTopLevel = modifyContext $ const []

-- * Adding to the context

-- | @addCtx x arg cont@ add a variable to the context.
--
--   Chooses an unused 'Name'.
{-# SPECIALIZE addCtx :: Name -> Dom Type -> TCM a -> TCM a #-}
addCtx :: MonadTCM tcm => Name -> Dom Type -> tcm a -> tcm a
addCtx x a ret = do
  ctx <- map (nameConcrete . fst . unDom) <$> getContext
  let x' = head $ filter (notTaken ctx) $ iterate nextName x
  ce <- mkContextEntry $ fmap ((,) x') a
  modifyContext (ce :) ret
      -- let-bindings keep track of own their context
  where
    notTaken xs x = isNoName (nameConcrete x) || nameConcrete x `notElem` xs

-- | N-ary variant of @addCtx@.
{-# SPECIALIZE addContext :: [Dom (Name, Type)] -> TCM a -> TCM a #-}
addContext :: MonadTCM tcm => [Dom (Name, Type)] -> tcm a -> tcm a
addContext ctx m =
  foldr (\arg -> addCtx (fst $ unDom arg) (fmap snd arg)) m ctx

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

-- | Context entries without a type have this dummy type.
dummyDom :: Dom Type
dummyDom = Common.Dom defaultArgInfo $ El Prop $ Sort Prop

-- | Go under an abstraction.
{-# SPECIALIZE underAbstraction :: Subst a => Dom Type -> Abs a -> (a -> TCM b) -> TCM b #-}
underAbstraction :: (Subst a, MonadTCM tcm) => Dom Type -> Abs a -> (a -> tcm b) -> tcm b
underAbstraction _ (NoAbs _ v) k = k v
underAbstraction t a k = do
    xs <- map (nameConcrete . fst . unDom) <$> getContext
    x <- freshName_ $ realName $ absName a
    let y = head $ filter (notTaken xs) $ iterate nextName x
    addCtx y t $ k $ absBody a
  where
    notTaken xs x = isNoName (nameConcrete x) || notElem (nameConcrete x) xs
    realName "_" = "x"
    realName s   = s

-- | Go under an abstract without worrying about the type to add to the context.
{-# SPECIALIZE underAbstraction_ :: Subst a => Abs a -> (a -> TCM b) -> TCM b #-}
underAbstraction_ :: (Subst a, MonadTCM tcm) => Abs a -> (a -> tcm b) -> tcm b
underAbstraction_ = underAbstraction dummyDom

-- | Add a telescope to the context.
{-# SPECIALIZE addCtxTel :: Telescope -> TCM a -> TCM a #-}
addCtxTel :: MonadTCM tcm => Telescope -> tcm a -> tcm a
addCtxTel EmptyTel	    ret = ret
addCtxTel (ExtendTel t tel) ret = underAbstraction t tel $ \tel -> addCtxTel tel ret


-- | Add a let bound variable
{-# SPECIALIZE addLetBinding :: ArgInfo -> Name -> Term -> Type -> TCM a -> TCM a #-}
addLetBinding :: MonadTCM tcm => ArgInfo -> Name -> Term -> Type -> tcm a -> tcm a
addLetBinding info x v t0 ret = do
    let t = Common.Dom (setArgInfoHiding NotHidden info) t0
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

-- | Generate [Var n - 1, .., Var 0] for all declarations in the context.
{-# SPECIALIZE getContextArgs :: TCM Args #-}
getContextArgs :: MonadTCM tcm => tcm Args
getContextArgs = do
  ctx <- getContext
  return $ reverse $ [ Common.Arg info $ var i | (Common.Dom info _, i) <- zip ctx [0..] ]

{-# SPECIALIZE getContextTerms :: TCM [Term] #-}
getContextTerms :: MonadTCM tcm => tcm [Term]
getContextTerms = map unArg <$> getContextArgs

-- | Get the current context as a 'Telescope' with the specified 'Hiding'.
{-# SPECIALIZE getContextTelescope :: TCM Telescope #-}
getContextTelescope :: MonadTCM tcm => tcm Telescope
getContextTelescope = foldr extTel EmptyTel . reverse <$> getContext
  where
    extTel (Common.Dom info (x, t)) = ExtendTel (Common.Dom info t) . Abs (show x)

-- | Check if we are in a compatible context, i.e. an extension of the given context.
{-# SPECIALIZE getContextId :: TCM [CtxId] #-}
getContextId :: MonadTCM tcm => tcm [CtxId]
getContextId = asks $ map ctxId . envContext

-- | get type of bound variable (i.e. deBruijn index)
--
{-# SPECIALIZE typeOfBV' :: Nat -> TCM (Dom Type) #-}
typeOfBV' :: MonadTCM tcm => Nat -> tcm (Dom Type)
typeOfBV' n =
    do	ctx <- getContext
	Common.Dom info (_,t) <- ctx !!! n
	return $ Common.Dom info $ raise (n + 1) t

{-# SPECIALIZE typeOfBV :: Nat -> TCM Type #-}
typeOfBV :: MonadTCM tcm => Nat -> tcm Type
typeOfBV i = unDom <$> typeOfBV' i

{-# SPECIALIZE nameOfBV :: Nat -> TCM Name #-}
nameOfBV :: MonadTCM tcm => Nat -> tcm Name
nameOfBV n =
    do	ctx <- getContext
	Common.Dom _ (x,_) <- ctx !!! n
	return x

-- | TODO: move(?)
xs !!! n = xs !!!! n
    where
	[]     !!!! _ = do
            ctx <- getContext
            fail $ "deBruijn index out of scope: " ++ show n ++ " in context " ++ show (map (fst . unDom) ctx)
	(x:_)  !!!! 0 = return x
	(_:xs) !!!! n = xs !!!! (n - 1)

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
                return (Var n [], t)
	    _	    ->
		case Map.lookup x def of
		    Just vt -> liftTCM $ getOpen vt
		    _	    -> fail $ "unbound variable " ++ show x
