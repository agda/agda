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
import Syntax.Scope

import TypeChecking.Monad
import TypeChecking.Monad.Debug
import TypeChecking.Monad.Options
import TypeChecking.Substitute

import Utils.Monad
import Utils.Fresh

#include "../../undefined.h"

-- | Get the name of the current module, if any.
currentModule :: TCM ModuleName
currentModule = asks envCurrentModule

-- | Set the name of the current module.
withCurrentModule :: ModuleName -> TCM a -> TCM a
withCurrentModule m =
    local $ \e -> e { envCurrentModule = m }

-- | Set the current scope.
setScope :: ScopeInfo -> TCM ()
setScope scope = modify $ \s -> s { stScopeInfo = scope }

-- | Get the current scope.
getScope :: TCM ScopeInfo
getScope = gets stScopeInfo


withScope :: ScopeInfo -> TCM a -> TCM a
withScope scope m =
    do	scope0 <- getScope
	setScope scope
	r <- m
	setScope scope0
        return r

-- | Set the current environment to the given 
withEnv :: TCEnv -> TCM a -> TCM a
withEnv env m = local (const env) m

-- | Get the current environmnet
getEnv :: TCM TCEnv
getEnv = ask

-- | Get the constraints
getConstraints :: TCM Constraints
getConstraints = gets stConstraints

lookupConstraint :: ConstraintId -> TCM (Signature,TCEnv,Constraint)
lookupConstraint i =
    do	cs <- getConstraints
	case Map.lookup i cs of
	    Just c  -> return c
	    _	    -> fail $ "no such constraint: " ++ show i

-- | Take constraints (clear all constraints).
takeConstraints :: TCM Constraints
takeConstraints =
    do	cs <- getConstraints
	modify $ \s -> s { stConstraints = Map.empty }
	return cs

-- | Get the meta store.
getMetaStore :: TCM MetaStore
getMetaStore = gets stMetaStore

-- | Lookup a meta variable
lookupMeta :: MetaId -> TCM MetaVariable
lookupMeta m =
    do	mmv <- Map.lookup m <$> getMetaStore
	case mmv of
	    Just mv -> return mv
	    _	    -> __IMPOSSIBLE__

-- | Reset the type checking state.
resetState :: TCM ()
resetState =
    do	opts <- commandLineOptions
	put initState
	setCommandLineOptions opts

-- | add a variable to the context
--
addCtx :: Name -> Type -> TCM a -> TCM a
addCtx x a = local (\e -> e { envContext = (x,a) : envContext e })

-- | Get the current context.
getContext :: TCM Context
getContext = asks envContext

getSignature :: TCM Signature
getSignature = gets stSignature

setSignature :: Signature -> TCM ()
setSignature sig = modify $ \s -> s { stSignature = sig }

withSignature :: Signature -> TCM a -> TCM a
withSignature sig m =
    do	sig0 <- getSignature
	setSignature sig
	r <- m
	setSignature sig0
        return r


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

-- | Add a constant to the signature. Lifts the definition to top level.
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
typeOfBV n =
    do	ctx <- getContext
	(_,t) <- ctx !!! n
	return $ raise (n + 1) t
    where
	[]     !!! _ = fail $ "deBruijn index out of scope: " ++ show n
	(x:_)  !!! 0 = return x
	(_:xs) !!! n = xs !!! (n - 1)

-- | Get the deBruijn index of a named variable
varIndex :: Name -> TCM Nat
varIndex x =
    do	ctx <- asks envContext
	case List.findIndex ((==x) . fst) ctx of
	    Just n  -> return n
	    _	    -> fail $ "unbound variable " ++ show x

-- | Lookup a module.
lookupModule :: ModuleName -> TCM ModuleDef
lookupModule m =
    do	sig <- getSignature
	case Map.lookup m sig of
	    Nothing -> fail $ show (getRange m) ++ ": no such module " ++ show m
	    Just md -> return md

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
	    Just d  -> return $ mkAbs ab $ d { defFreeVars = length tel }
    where
	m = qnameModule q
	x = qnameName q
	mkAbs True d =
	    case makeAbstract d of
		Just d	-> d
		Nothing	-> __IMPOSSIBLE__
	mkAbs False d = d

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

escapeContext :: Int -> TCM a -> TCM a
escapeContext n = local $ \e -> e { envContext = drop n $ envContext e }


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

---------------------------------------------------------------------------
-- * Meta variables
---------------------------------------------------------------------------

createMetaInfo :: TCM MetaInfo
createMetaInfo = 
    do  r <- getCurrentRange
        s <- getScope
        env <- ask 
        sig <- getSignature 
        return $ MetaInfo r s env sig

addInteractionPoint :: InteractionId -> MetaId -> TCM ()
addInteractionPoint ii mi =
    modify $ \s -> s { stInteractionPoints =
			Map.insert ii mi $ stInteractionPoints s
		     }


removeInteractionPoint :: InteractionId -> TCM ()
removeInteractionPoint ii =
    modify $ \s -> s { stInteractionPoints =
			Map.delete ii $ stInteractionPoints s
		     }


getInteractionPoints :: TCM [InteractionId]
getInteractionPoints = keys <$> gets stInteractionPoints

lookupInteractionId :: InteractionId -> TCM MetaId
lookupInteractionId ii = 
    do  mmi <- Map.lookup ii <$> gets stInteractionPoints
	case mmi of
	    Just mi -> return mi
	    _	    -> __IMPOSSIBLE__

judgementInteractionId :: InteractionId -> TCM (Judgement Type Sort MetaId)
judgementInteractionId ii = 
    do  mi <- lookupInteractionId ii
        mvJudgement  <$> lookupMeta mi
        


-- | Generate new meta variable.
newMeta :: MetaInfo -> Judgement Type Sort a -> TCM MetaId
newMeta mi j =
    do	x <- fresh
	let mv = MetaVar mi (fmap (const x) j) Open
	modify (\st -> st{stMetaStore = Map.insert x mv $ stMetaStore st})
	return x

---------------------------------------------------------------------------
-- * Trace
---------------------------------------------------------------------------

getTrace :: TCM Trace
getTrace = gets stTrace

setCurrentRange :: HasRange a => a -> TCM ()
setCurrentRange x = modify $ \s -> s { stTrace = (stTrace s) { traceRange = getRange x } }

getCurrentRange :: TCM Range
getCurrentRange = getRange <$> getTrace

withRange :: Range -> TCM a -> TCM a
withRange r m =
    do	r0 <- getCurrentRange
	setCurrentRange r
	x <- m
	setCurrentRange r0
	return x


withMetaInfo :: MetaInfo -> TCM a -> TCM a
withMetaInfo mI m = 
          withRange (metaRange mI) 
        $ withScope (metaScope mI) 
        $ withSignature (metaSig mI) 
        $ withEnv (metaEnv mI) m


