{-# OPTIONS -cpp #-}

module TypeChecking.Monad.Context where

import Control.Monad.Reader
import Data.List hiding (sort)
import qualified Data.Map as Map

import Syntax.Concrete.Name (isNoName)
import Syntax.Abstract.Name
import Syntax.Common
import Syntax.Internal
import Syntax.Scope.Base
import TypeChecking.Monad.Base
import TypeChecking.Substitute
import TypeChecking.Monad.Open

import Utils.Monad
import Utils.Fresh

#include "../../undefined.h"
import Utils.Impossible

mkContextEntry :: MonadTCM tcm => Arg (Name, Type) -> tcm ContextEntry
mkContextEntry x = do
  i <- fresh
  return $ Ctx i x

-- | add a variable to the context
--
addCtx :: MonadTCM tcm => Name -> Arg Type -> tcm a -> tcm a
addCtx x a ret = do
  ctx <- map (nameConcrete . fst . unArg) <$> getContext
  let x' = head $ filter (notTaken ctx) $ iterate nextName x
  ce <- mkContextEntry $ fmap ((,) x') a
  flip local ret $ \e -> e { envContext = ce : envContext e }
      -- let-bindings keep track of own their context
  where
    notTaken xs x = isNoName (nameConcrete x) || nameConcrete x `notElem` xs

-- | Change the context
inContext :: MonadTCM tcm => [Arg (Name, Type)] -> tcm a -> tcm a
inContext xs ret = do
  ctx <- mapM mkContextEntry xs
  flip local ret $ \e -> e { envContext = ctx }

-- | Go under an abstraction.
underAbstraction :: MonadTCM tcm => Arg Type -> Abs a -> (a -> tcm b) -> tcm b
underAbstraction t a k = do
    xs <- map (nameConcrete . fst . unArg) <$> getContext
    x <- freshName_ $ realName $ absName a
    let y = head $ filter (notTaken xs) $ iterate nextName x
    addCtx y t $ k $ absBody a
  where
    notTaken xs x = notElem (nameConcrete x) xs
    realName "_" = "z"
    realName s   = s

-- | Go under an abstract without worrying about the type to add to the context.
underAbstraction_ :: MonadTCM tcm => Abs a -> (a -> tcm b) -> tcm b
underAbstraction_ = underAbstraction (Arg NotHidden $ sort Prop)

-- | Add a telescope to the context.
addCtxTel :: MonadTCM tcm => Telescope -> tcm a -> tcm a
addCtxTel EmptyTel	    ret = ret
addCtxTel (ExtendTel t tel) ret = underAbstraction t tel $ \tel -> addCtxTel tel ret

-- | Get the current context.
getContext :: MonadTCM tcm => tcm [Arg (Name, Type)]
getContext = asks $ map ctxEntry . envContext

-- | Generate [Var n - 1, .., Var 0] for all declarations in the context.
getContextArgs :: MonadTCM tcm => tcm Args
getContextArgs = do
  ctx <- getContext
  return $ reverse $ [ Arg h $ Var i [] | (Arg h _, i) <- zip ctx [0..] ]

getContextTerms :: MonadTCM tcm => tcm [Term]
getContextTerms = map unArg <$> getContextArgs

-- | Get the current context as a 'Telescope' with the specified 'Hiding'.
getContextTelescope :: MonadTCM tcm => tcm Telescope
getContextTelescope = foldr extTel EmptyTel . reverse <$> getContext
  where
    extTel (Arg h (x, t)) = ExtendTel (Arg h t) . Abs (show x)

-- | add a bunch of variables with the same type to the context
addCtxs :: MonadTCM tcm => [Name] -> Arg Type -> tcm a -> tcm a
addCtxs []     _ k = k
addCtxs (x:xs) t k = addCtx x t $ addCtxs xs (raise 1 t) k

-- | Check if we are in a compatible context, i.e. an extension of the given context.
getContextId :: MonadTCM tcm => tcm [CtxId]
getContextId = asks $ map ctxId . envContext

-- | Add a let bound variable
addLetBinding :: MonadTCM tcm => Name -> Term -> Type -> tcm a -> tcm a
addLetBinding x v t ret = do
    vt <- makeOpen (v, t)
    flip local ret $ \e -> e { envLetBindings = Map.insert x vt $ envLetBindings e }

-- | get type of bound variable (i.e. deBruijn index)
--
typeOfBV' :: MonadTCM tcm => Nat -> tcm (Arg Type)
typeOfBV' n =
    do	ctx <- getContext
	Arg h (_,t) <- ctx !!! n
	return $ Arg h $ raise (n + 1) t

typeOfBV :: MonadTCM tcm => Nat -> tcm Type
typeOfBV i = unArg <$> typeOfBV' i

nameOfBV :: MonadTCM tcm => Nat -> tcm Name
nameOfBV n =
    do	ctx <- getContext
	Arg _ (x,_) <- ctx !!! n
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
getVarInfo :: MonadTCM tcm => Name -> tcm (Term, Type)
getVarInfo x =
    do	ctx <- getContext
	def <- asks envLetBindings
	case findIndex ((==x) . fst . unArg) ctx of
	    Just n  ->
		do  t <- typeOfBV n
		    return (Var n [], t)
	    _	    ->
		case Map.lookup x def of
		    Just vt -> getOpen vt
		    _	    -> fail $ "unbound variable " ++ show x

escapeContext :: MonadTCM tcm => Int -> tcm a -> tcm a
escapeContext n = local $ \e -> e { envContext = drop n $ envContext e }

