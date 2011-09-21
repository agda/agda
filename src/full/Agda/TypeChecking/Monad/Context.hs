{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Context where

import Control.Monad.Reader
import Data.List hiding (sort)
import qualified Data.Map as Map

import Agda.Syntax.Concrete.Name (isNoName)
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Scope.Base
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Open

import Agda.Utils.Monad
import Agda.Utils.Fresh

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Modify the 'ctxEntry' field of a 'ContextEntry'.
modifyContextEntry :: (Arg (Name, Type) -> Arg (Name, Type)) -> ContextEntry -> ContextEntry
modifyContextEntry f ce = ce { ctxEntry = f (ctxEntry ce) }

-- | Modify all 'ContextEntry's.
modifyContextEntries :: (Arg (Name, Type) -> Arg (Name, Type)) -> Context -> Context
modifyContextEntries f = map (modifyContextEntry f)

-- | Modify a 'Context' in a computation.
{-# SPECIALIZE modifyContext :: (Context -> Context) -> TCM a -> TCM a #-}
modifyContext :: MonadTCM tcm => (Context -> Context) -> tcm a -> tcm a
modifyContext f = local $ \ e -> e { envContext = f (envContext e) }

{-# SPECIALIZE mkContextEntry :: Arg (Name, Type) -> TCM ContextEntry #-}
mkContextEntry :: MonadTCM tcm => Arg (Name, Type) -> tcm ContextEntry
mkContextEntry x = do
  i <- fresh
  return $ Ctx i x

-- | @addCtx x arg cont@ add a variable to the context.
--
--   Chooses an unused 'Name'.
{-# SPECIALIZE addCtx :: Name -> Arg Type -> TCM a -> TCM a #-}
addCtx :: MonadTCM tcm => Name -> Arg Type -> tcm a -> tcm a
addCtx x a ret = do
  ctx <- map (nameConcrete . fst . unArg) <$> getContext
  let x' = head $ filter (notTaken ctx) $ iterate nextName x
  ce <- mkContextEntry $ fmap ((,) x') a
  flip local ret $ \e -> e { envContext = ce : envContext e }
      -- let-bindings keep track of own their context
  where
    notTaken xs x = isNoName (nameConcrete x) || nameConcrete x `notElem` xs

-- | N-ary variant of @addCtx@.
{-# SPECIALIZE addContext :: [Arg (Name, Type)] -> TCM a -> TCM a #-}
addContext :: MonadTCM tcm => [Arg (Name, Type)] -> tcm a -> tcm a
addContext ctx m =
  foldr (\arg -> addCtx (fst $ unArg arg) (fmap snd arg)) m ctx

-- | Turns the string into a name and adds it to the context.
{-# SPECIALIZE addCtxString :: String -> Arg Type -> TCM a -> TCM a #-}
addCtxString :: MonadTCM tcm => String -> Arg Type -> tcm a -> tcm a
addCtxString s a m = do
  x <- freshName_ s
  addCtx x a m

-- | Change the context
{-# SPECIALIZE inContext :: [Arg (Name, Type)] -> TCM a -> TCM a #-}
inContext :: MonadTCM tcm => [Arg (Name, Type)] -> tcm a -> tcm a
inContext xs ret = do
  ctx <- mapM mkContextEntry xs
  flip local ret $ \e -> e { envContext = ctx }

-- | Go under an abstraction.
{-# SPECIALIZE underAbstraction :: Raise a => Arg Type -> Abs a -> (a -> TCM b) -> TCM b #-}
underAbstraction :: (Raise a, MonadTCM tcm) => Arg Type -> Abs a -> (a -> tcm b) -> tcm b
underAbstraction t a k = do
    xs <- map (nameConcrete . fst . unArg) <$> getContext
    x <- freshName_ $ realName $ absName a
    let y = head $ filter (notTaken xs) $ iterate nextName x
    addCtx y t $ k $ absBody a
  where
    notTaken xs x = notElem (nameConcrete x) xs
    realName "_" = "y"
    realName s   = s

-- | Go under an abstract without worrying about the type to add to the context.
{-# SPECIALIZE underAbstraction_ :: Raise a => Abs a -> (a -> TCM b) -> TCM b #-}
underAbstraction_ :: (Raise a, MonadTCM tcm) => Abs a -> (a -> tcm b) -> tcm b
underAbstraction_ = underAbstraction (Arg NotHidden Relevant $ sort Prop)

-- | Add a telescope to the context.
{-# SPECIALIZE addCtxTel :: Telescope -> TCM a -> TCM a #-}
addCtxTel :: MonadTCM tcm => Telescope -> tcm a -> tcm a
addCtxTel EmptyTel	    ret = ret
addCtxTel (ExtendTel t tel) ret = underAbstraction t tel $ \tel -> addCtxTel tel ret

-- | Get the current context.
{-# SPECIALIZE getContext :: TCM [Arg (Name, Type)] #-}
getContext :: MonadTCM tcm => tcm [Arg (Name, Type)]
getContext = asks $ map ctxEntry . envContext

-- | Generate [Var n - 1, .., Var 0] for all declarations in the context.
{-# SPECIALIZE getContextArgs :: TCM Args #-}
getContextArgs :: MonadTCM tcm => tcm Args
getContextArgs = do
  ctx <- getContext
  return $ reverse $ [ Arg h r $ Var i [] | (Arg h r _, i) <- zip ctx [0..] ]

{-# SPECIALIZE getContextTerms :: TCM [Term] #-}
getContextTerms :: MonadTCM tcm => tcm [Term]
getContextTerms = map unArg <$> getContextArgs

-- | Get the current context as a 'Telescope' with the specified 'Hiding'.
{-# SPECIALIZE getContextTelescope :: TCM Telescope #-}
getContextTelescope :: MonadTCM tcm => tcm Telescope
getContextTelescope = foldr extTel EmptyTel . reverse <$> getContext
  where
    extTel (Arg h r (x, t)) = ExtendTel (Arg h r t) . Abs (show x)

-- | add a bunch of variables with the same type to the context
{-# SPECIALIZE addCtxs :: [Name] -> Arg Type -> TCM a -> TCM a #-}
addCtxs :: MonadTCM tcm => [Name] -> Arg Type -> tcm a -> tcm a
addCtxs []     _ k = k
addCtxs (x:xs) t k = addCtx x t $ addCtxs xs (raise 1 t) k

-- | Check if we are in a compatible context, i.e. an extension of the given context.
{-# SPECIALIZE getContextId :: TCM [CtxId] #-}
getContextId :: MonadTCM tcm => tcm [CtxId]
getContextId = asks $ map ctxId . envContext

-- | Add a let bound variable
{-# SPECIALIZE addLetBinding :: Relevance -> Name -> Term -> Type -> TCM a -> TCM a #-}
addLetBinding :: MonadTCM tcm => Relevance -> Name -> Term -> Type -> tcm a -> tcm a
addLetBinding rel x v t0 ret = do
    let t = Arg NotHidden rel t0
    vt <- liftTCM $ makeOpen (v, t)
    flip local ret $ \e -> e { envLetBindings = Map.insert x vt $ envLetBindings e }

-- | get type of bound variable (i.e. deBruijn index)
--
{-# SPECIALIZE typeOfBV' :: Nat -> TCM (Arg Type) #-}
typeOfBV' :: MonadTCM tcm => Nat -> tcm (Arg Type)
typeOfBV' n =
    do	ctx <- getContext
	Arg h r (_,t) <- ctx !!! n
	return $ Arg h r $ raise (n + 1) t

{-# SPECIALIZE typeOfBV :: Nat -> TCM Type #-}
typeOfBV :: MonadTCM tcm => Nat -> tcm Type
typeOfBV i = unArg <$> typeOfBV' i

{-# SPECIALIZE nameOfBV :: Nat -> TCM Name #-}
nameOfBV :: MonadTCM tcm => Nat -> tcm Name
nameOfBV n =
    do	ctx <- getContext
	Arg _ _ (x,_) <- ctx !!! n
	return x

-- | TODO: move(?)
xs !!! n = xs !!!! n
    where
	[]     !!!! _ = do
            ctx <- getContext
            fail $ "deBruijn index out of scope: " ++ show n ++ " in context " ++ show (map (fst . unArg) ctx)
	(x:_)  !!!! 0 = return x
	(_:xs) !!!! n = xs !!!! (n - 1)

-- | Get the term corresponding to a named variable. If it is a lambda bound
--   variable the deBruijn index is returned and if it is a let bound variable
--   its definition is returned.
{-# SPECIALIZE getVarInfo :: Name -> TCM (Term, Arg Type) #-}
getVarInfo :: MonadTCM tcm => Name -> tcm (Term, Arg Type)
getVarInfo x =
    do	ctx <- getContext
	def <- asks envLetBindings
	case findIndex ((==x) . fst . unArg) ctx of
	    Just n0 ->
		do  let n = fromIntegral n0
                    t <- typeOfBV' n
		    return (Var n [], t)
	    _	    ->
		case Map.lookup x def of
		    Just vt -> liftTCM $ getOpen vt
		    _	    -> fail $ "unbound variable " ++ show x

{-# SPECIALIZE escapeContext :: Int -> TCM a -> TCM a #-}
escapeContext :: MonadTCM tcm => Int -> tcm a -> tcm a
escapeContext n = local $ \e -> e { envContext = drop n $ envContext e }
