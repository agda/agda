{-# OPTIONS -cpp #-}

module TypeChecking.Monad.Context where

import Control.Monad.Reader
import Control.Monad.State
import Data.List as List
import Data.Map as Map
import Data.Maybe

import Syntax.Position
import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.Monad.Debug
import TypeChecking.Substitute
import Utils.Monad

__debug = debug

#include "../../undefined.h"

-- | Get the name of the current module, if any.
currentModule :: TCM ModuleName
currentModule = asks envCurrentModule

-- | Set the name of the current module.
withCurrentModule :: ModuleName -> TCM a -> TCM a
withCurrentModule m =
    local $ \e -> e { envCurrentModule = m }

-- | add a variable to the context
--
addCtx :: Name -> Type -> TCM a -> TCM a
addCtx x a = local (\e -> e { envContext = (x,a) : envContext e })

-- | Get the current context.
getContext :: TCM Context
getContext = asks envContext

getSignature :: TCM Signature
getSignature = gets stSignature

-- | Get the current context as a 'Telescope' (everything 'Hidden').
getContextTelescope :: TCM Telescope
getContextTelescope = List.map (Arg Hidden . snd) . reverse <$> getContext

-- | add a bunch of variables with the same type to the context
addCtxs :: [Name] -> Type -> TCM a -> TCM a
addCtxs []     _ k = k
addCtxs (x:xs) t k = addCtx x t $ addCtxs xs (raise 1 t) k

-- | Add a telescope to the context. Uses dummy names.
addCtxTel :: Telescope -> TCM a -> TCM a
addCtxTel [] ret = ret
addCtxTel (Arg _ t : tel) ret =
    do	x <- freshNoName_
	addCtx x t $ addCtxTel tel ret

-- | Add a constant to the signature.
addConstant :: QName -> Definition -> TCM ()
addConstant q d =
    do	tel <- getContextTelescope
	let d' = abstract tel d
-- 	debug $ "addConstant " ++ show q ++ " " ++ show tel ++ " " ++ show d'
	modify $ \s ->
	    s { stSignature = 
		    Map.adjust (\md -> md { mdefDefs = Map.insert x d'
						     $ mdefDefs md
					  }
			       ) m $ stSignature s
	      }
    where
	m = qnameModule q
	x = qnameName q
    -- modify $ \s -> s { stSignature = Map.insert q d $ stSignature s }

-- | Add a defined module.
addModule :: ModuleName -> ModuleDef -> TCM ()
addModule m d = modify $ \s -> s { stSignature = Map.insert m d $ stSignature s }

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

-- | Always returns 'MExplicit' (instantiates modules on the fly).
lookupModule :: ModuleName -> TCM ModuleDef
lookupModule m =
    do	sig <- getSignature
	case Map.lookup m sig of
	    Nothing -> fail $ show (getRange m) ++ ": no such module " ++ show m
	    Just (MDef _ tel n m' args)	->
		do  defs <- mdefDefs <$> lookupModule m'
		    return $ MExplicit
			     { mdefName      = m
			     , mdefTelescope = tel
			     , mdefNofParams = n
			     , mdefDefs      = Map.map inst defs
			     }
		where
		    inst d = abstract tel $ d `apply` args
	    Just md -> return md

-- | Lookup the definition of a name. The result is a closed thing, all free
--   variables have been abstracted over.
getConstInfo :: QName -> TCM Definition
getConstInfo q =
    do	md <- lookupModule m
	let tel  = mdefTelescope md
	    defs = mdefDefs md
	case Map.lookup x defs of
	    Nothing -> fail $ show (getRange q) ++ ": no such name " ++ show x ++ " in module " ++ show m
	    Just d  -> return $ d { defFreeVars = length tel }
    where
	m = qnameModule q
	x = qnameName q

-- | Instantiate a closed definition with the correct part of the current
--   context. Precondition: the variables abstracted over should be a prefix of
--   the current context. This will be satisfied for a name looked up during
--   type checking.
instantiateDef :: Definition -> TCM Definition
instantiateDef d =
    do	ctx <- asks envContext
	let n  = defFreeVars d
	    k  = length ctx - n
	    vs = reverse [ Arg Hidden $ Var (i + k) [] | i <- [0..n - 1] ]
-- 	debug $ "instDef " ++ show d
-- 	debug $ "        " ++ show vs
-- 	debug $ "   ---> " ++ show (apply d vs)
	return $ d `apply` vs

-- | Give the abstract view of a definition.
makeAbstract :: Definition -> Maybe Definition
makeAbstract d = do def <- makeAbs $ theDef d
		    return d { theDef = def }
    where
	makeAbs (Datatype _ _ AbstractDef)    = Just Axiom
	makeAbs (Function _ AbstractDef)      = Just Axiom
	makeAbs (Constructor _ _ AbstractDef) = Nothing
	makeAbs d			      = Just d

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
    | envAbstractMode env = True
    | otherwise		  = not $ m `isSubModuleOf` qnameModule q
    where
	m = envCurrentModule env

-- | get type of a constant 
--
typeOfConst :: QName -> TCM Type
typeOfConst q = defType <$> (instantiateDef =<< getConstInfo q)


escapeContext :: Int -> TCM a -> TCM a
escapeContext n = local $ \e -> e { envContext = drop n $ envContext e }


-- | Get the canonical name of a constructor (i.e. the module in which it was defined).
canonicalConstructor :: QName -> TCM QName
canonicalConstructor q =
    do	m <- chaseModule $ qnameModule q
	return $ q { qnameModule = m }
    where
	chaseModule m =
	    do	md <- lookupModule m
		case md of
		    MDef _ _ _ m' _   -> chaseModule m'
		    MExplicit m _ _ _ -> return m

-- | Do something for each module with a certain kind of name.
forEachModule :: (ModuleName -> Bool) -> (ModuleName -> TCM a) -> TCM [a]
forEachModule p go =
    do	sig <- getSignature
	concat <$> mapM action (Map.keys sig)
    where
	action m
	    | p m	= (:[]) <$> go m
	    | otherwise = return []

forEachModule_ :: (ModuleName -> Bool) -> (ModuleName -> TCM a) -> TCM ()
forEachModule_ p go = forEachModule p go >> return ()

