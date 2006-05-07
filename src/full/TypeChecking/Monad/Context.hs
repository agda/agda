{-# OPTIONS -cpp #-}

module TypeChecking.Monad.Context where

import Control.Monad.Reader
import Control.Monad.State
import Data.List as List
import Data.Map as Map
import Data.Maybe

import Syntax.Common
import Syntax.Internal
import Syntax.Position
import TypeChecking.Monad
import TypeChecking.Monad.Debug
import TypeChecking.Substitute
import Utils.Monad

__debug = debug

#include "../../undefined.h"

-- | Get the name of the current module, if any.
currentModule :: TCM (Maybe ModuleName)
currentModule = asks envCurrentModule

-- | Get the name of the current module. Assumes there is one.
currentModule_ :: TCM ModuleName
currentModule_ =
    do	m <- currentModule
	case m of
	    Just m  -> return m
	    Nothing -> fail "panic: no current module!"

-- | Set the name of the current module.
withCurrentModule :: ModuleName -> TCM a -> TCM a
withCurrentModule m =
    local $ \e -> e { envCurrentModule = Just m }

-- | add a variable to the context
--
addCtx :: Name -> Type -> TCM a -> TCM a
addCtx x a = local (\e -> e { envContext = (x,a) : envContext e })

-- | add a bunch of variables with the same type to the context
addCtxs :: [Name] -> Type -> TCM a -> TCM a
addCtxs []     _ k = k
addCtxs (x:xs) t k = addCtx x t $ addCtxs xs (raise 1 t) k

-- | Add a constant to the signature.
addConstant :: QName -> Definition -> TCM ()
addConstant q d = modify $ \s -> s { stSignature = Map.insert q d $ stSignature s }

-- | get type of bound variable (i.e. deBruijn index)
--
typeOfBV :: Nat -> TCM Type
typeOfBV n = do
    ctx <- asks envContext
    return $ raise (n + 1) $ snd $ ctx !! n

-- | Get the deBruijn index of a named variable
varIndex :: Name -> TCM Nat
varIndex x =
    do	ctx <- asks envContext
	case List.findIndex ((==x) . fst) ctx of
	    Just n  -> return n
	    _	    -> fail $ "unbound variable " ++ show x

getConstInfo :: QName -> TCM Definition
getConstInfo q =
    do	sig <- gets stSignature
	a   <- treatAbstractly q
	let abstract = if a then makeAbstract else Just
	case abstract =<< Map.lookup q sig of
	    Just d  -> return d
	    _	    -> fail $ show (getRange q) ++ ": " ++ show q ++ " is not in scope."

-- | Give the abstract view of a definition.
makeAbstract :: Definition -> Maybe Definition
makeAbstract (Datatype t _ _ AbstractDef)    = Just $ Axiom t
makeAbstract (Function _ t AbstractDef)	     = Just $ Axiom t
makeAbstract (Constructor _ _ _ AbstractDef) = Nothing
makeAbstract d				     = Just d

makeAbstract' :: TCEnv -> QName -> Definition -> Maybe Definition
makeAbstract' env q d
    | treatAbstractly' q env = makeAbstract d
    | otherwise		     = Just d

-- | Enter abstract mode
inAbstractMode :: TCM a -> TCM a
inAbstractMode = local $ \e -> e { envAbstractMode = True }

-- | Check whether a name might have to be treated abstractly (either if we're
--   'inAbstractMode' or it's not a local name). Returns true for things not
--   declared abstract as well, but for those 'makeAbstract' will have no effect.
treatAbstractly :: QName -> TCM Bool
treatAbstractly q = treatAbstractly' q <$> ask

treatAbstractly' :: QName -> TCEnv -> Bool
treatAbstractly' q env
    | envAbstractMode env	       = True
    | isNothing $ envCurrentModule env = True
    | otherwise			       = not $ m `isSubModuleOf` qnameModule q
    where
	Just m = envCurrentModule env

-- | get type of a constant 
--
typeOfConst :: QName -> TCM Type
typeOfConst q = defType <$> getConstInfo q


escapeContext :: Int -> TCM a -> TCM a
escapeContext n = local $ \e -> e { envContext = drop n $ envContext e }

