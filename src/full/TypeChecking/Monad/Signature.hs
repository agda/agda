{-# OPTIONS -cpp #-}
module TypeChecking.Monad.Signature where

import Control.Monad.State
import Control.Monad.Reader
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List

import Syntax.Abstract.Name
import Syntax.Common
import Syntax.Internal
import Syntax.Position

import TypeChecking.Monad.Base
import TypeChecking.Monad.Context
import TypeChecking.Substitute

import Utils.Monad
import Utils.Map as Map
import Utils.Size

#include "../../undefined.h"

modifySignature :: MonadTCM tcm => (Signature -> Signature) -> tcm ()
modifySignature f = modify $ \s -> s { stSignature = f $ stSignature s }

getSignature :: MonadTCM tcm => tcm Signature
getSignature = liftTCM $ gets stSignature

getImportedSignature :: MonadTCM tcm => tcm Signature
getImportedSignature = liftTCM $ gets stImports

setSignature :: MonadTCM tcm => Signature -> tcm ()
setSignature sig = modifySignature $ const sig

setImportedSignature :: MonadTCM tcm => Signature -> tcm ()
setImportedSignature sig = liftTCM $ modify $ \s -> s { stImports = sig }

withSignature :: MonadTCM tcm => Signature -> tcm a -> tcm a
withSignature sig m =
    do	sig0 <- getSignature
	setSignature sig
	r <- m
	setSignature sig0
        return r

-- | Add a constant to the signature. Lifts the definition to top level.
addConstant :: MonadTCM tcm => QName -> Definition -> tcm ()
addConstant q d = liftTCM $ do
  tel <- getContextTelescope
  modifySignature $ \sig -> sig
    { sigDefinitions = Map.insert q (abstract tel d) $ sigDefinitions sig }

unionSignatures :: [Signature] -> Signature
unionSignatures ss = foldr unionSignature emptySignature ss
  where
    unionSignature (Sig a b) (Sig c d) = Sig (Map.union a c) (Map.union b d)

-- | Add a section to the signature.
addSection :: MonadTCM tcm => ModuleName -> Telescope -> tcm ()
addSection m tel = do
  top <- getContextTelescope
  let tel' = abstract top tel
  modifySignature $ \sig -> sig { sigSections = Map.insert m tel' $ sigSections sig }

-- | Lookup a section. If it doesn't exist that just means that the module
--   wasn't parameterised.
lookupSection :: MonadTCM tcm => ModuleName -> tcm Telescope
lookupSection m = do
  sig  <- sigSections <$> getSignature
  isig <- sigSections <$> getImportedSignature
  return $ maybe EmptyTel id $ Map.lookup m sig `mplus` Map.lookup m isig

applySection :: MonadTCM tcm => ModuleName -> ModuleName -> Telescope -> Args -> tcm ()
applySection new old tel ts = liftTCM $ do
  sig <- getSignature
  let ss = Map.toList $ Map.filterKeys partOfOld $ sigSections sig
      ds = Map.toList $ Map.filterKeys partOfOld $ sigDefinitions sig
  ts0 <- take (size tel - size ts) <$> getContextArgs
  mapM_ (copyDef $ ts0 ++ ts) ds
  mapM_ (copySec $ ts0 ++ ts) ss
  where
    partOfOld x = x `isSubModuleOf` old

    copyName x = qualifyQ new . qnameFromList . drop (size old) . qnameToList $ x

    -- TODO!!: constructors
    copyDef :: Args -> (QName, Definition) -> TCM ()
    copyDef ts (x, d) = addConstant (copyName x) (apply d ts)

    copySec :: Args -> (QName, Telescope) -> TCM ()
    copySec ts (x, tel) = addSection (copyName x) (apply tel ts)

-- | Lookup the definition of a name. The result is a closed thing, all free
--   variables have been abstracted over.
getConstInfo :: MonadTCM tcm => QName -> tcm Definition
getConstInfo q = liftTCM $ do
  ab   <- treatAbstractly q
  defs <- sigDefinitions <$> getSignature
  case Map.lookup q defs of
      Nothing -> fail $ show (getRange q) ++ ": no such name " ++ show q
      Just d  -> mkAbs ab d
  where
    mkAbs True d =
      case makeAbstract d of
	Just d	-> return d
	Nothing	-> fail $ "panic: Not in scope " ++ show q -- __IMPOSSIBLE__
    mkAbs False d = return d

-- | Instantiate a closed definition with the correct part of the current
--   context. Precondition: the variables abstracted over should be a prefix of
--   the current context. This will be satisfied for a name looked up during
--   type checking.
instantiateDef :: MonadTCM tcm => Definition -> tcm Definition
instantiateDef d =
    do	ctx <- liftTCM $ asks envContext
	let n  = defFreeVars d
	    k  = size ctx - n
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
	makeAbs (Datatype _ _ _ _ AbstractDef) = Just Axiom
	makeAbs (Function _ AbstractDef)       = Just Axiom
	makeAbs (Constructor _ _ AbstractDef)  = Nothing
	makeAbs d			       = Just d

-- | Enter abstract mode
inAbstractMode :: MonadTCM tcm => tcm a -> tcm a
inAbstractMode = local $ \e -> e { envAbstractMode = True }

-- | Check whether a name might have to be treated abstractly (either if we're
--   'inAbstractMode' or it's not a local name). Returns true for things not
--   declared abstract as well, but for those 'makeAbstract' will have no effect.
treatAbstractly :: MonadTCM tcm => QName -> tcm Bool
treatAbstractly q = treatAbstractly' q <$> ask

treatAbstractly' :: QName -> TCEnv -> Bool
treatAbstractly' q env
  | envAbstractMode env = True
  | otherwise		= not $ current `isSubModuleOf` m
  where
    current = envCurrentModule env
    m	    = qnameFromList $ qnameModule q

-- | get type of a constant 
typeOfConst :: MonadTCM tcm => QName -> tcm Type
typeOfConst q = defType <$> (instantiateDef =<< getConstInfo q)

-- | The name must be a datatype.
sortOfConst :: MonadTCM tcm => QName -> tcm Sort
sortOfConst q =
    do	d <- theDef <$> getConstInfo q
	case d of
	    Datatype _ _ _ s _	-> return s
	    _			-> fail $ "Expected " ++ show q ++ " to be a datatype."

