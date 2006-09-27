{-# OPTIONS -cpp #-}
module TypeChecking.Monad.Signature where

import Control.Monad.State
import Control.Monad.Reader
import Data.Map as Map
import Data.List as List

import Syntax.Abstract.Name
import Syntax.Common
import Syntax.Internal
import Syntax.Position

import TypeChecking.Monad.Base
import TypeChecking.Monad.Context
import TypeChecking.Substitute

import Utils.Monad

#include "../../undefined.h"

getSignature :: TCM Signature
getSignature = gets stSignature

getImportedSignature :: TCM Signature
getImportedSignature = gets stImports

setSignature :: Signature -> TCM ()
setSignature sig = modify $ \s -> s { stSignature = sig }

setImportedSignature :: Signature -> TCM ()
setImportedSignature sig = modify $ \s -> s { stImports = sig }

withSignature :: Signature -> TCM a -> TCM a
withSignature sig m =
    do	sig0 <- getSignature
	setSignature sig
	r <- m
	setSignature sig0
        return r

-- | Add a constant to the signature. Lifts the definition to top level.
addConstant :: QName -> Definition -> TCM ()
addConstant q d =
    do	tel <- getContextTelescope
	let d' = abstract tel d
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

-- | Lookup a module.
lookupModule :: ModuleName -> TCM ModuleDef
lookupModule m =
    do	sig  <- getSignature
	isig <- getImportedSignature
	case (Map.lookup m sig, Map.lookup m isig) of
	    (Nothing, Nothing) -> fail $ show (getRange m) ++ ": no such module " ++ show m
	    (Just md, Nothing) -> return md
	    (Nothing, Just md) -> return md
	    (Just _, Just _)   -> typeError $ LocalVsImportedModuleClash m

implicitModuleDefs :: Telescope -> ModuleName -> Args -> Definitions -> Definitions
implicitModuleDefs tel m args defs = Map.mapWithKey redirect defs
    where
	redirect x d = abstract (List.map hide tel)
			$ setDef
			$ d `apply` args'
	    where
		hide (Arg _ x) = Arg Hidden x
		args' = List.map hide args
		old = theDef d
		mkRHS = case old of
			    Constructor _ _ _ -> Con
			    _		      -> Def
		clause = Clause [] $ Body $ mkRHS (qualify m x) args'
		setDef d = d { theDef = Function [clause] ConcreteDef }

-- | Lookup the definition of a name. The result is a closed thing, all free
--   variables have been abstracted over.
getConstInfo :: QName -> TCM Definition
getConstInfo q =
    do	ab <- treatAbstractly q
	md <- lookupModule m
	let tel  = mdefTelescope md
	    defs = mdefDefs md
	case Map.lookup x defs of
	    Nothing -> fail $ show (getRange q) ++ ": no such name " ++ show x ++ " in module " ++ show m
	    Just d  -> mkAbs ab d
    where
	m = qnameModule q
	x = qnameName q
	mkAbs True d =
	    case makeAbstract d of
		Just d	-> return d
		Nothing	-> fail $ "Not in scope " ++ show q -- __IMPOSSIBLE__
	mkAbs False d = return d

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
	makeAbs (Datatype _ _ _ AbstractDef)  = Just Axiom
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
typeOfConst :: QName -> TCM Type
typeOfConst q = defType <$> (instantiateDef =<< getConstInfo q)

-- | The name must be a datatype.
sortOfConst :: QName -> TCM Sort
sortOfConst q =
    do	d <- theDef <$> getConstInfo q
	case d of
	    Datatype _ _ s _	-> return s
	    _			-> fail $ "Expected " ++ show q ++ " to be a datatype."

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

