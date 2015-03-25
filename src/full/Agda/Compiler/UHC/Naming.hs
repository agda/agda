{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Converts Agda names to Haskell/Core names.
--
-- There are the following type of names in Agda:
-- - function names
-- - datatype names
-- - constructor names
--
-- All names in a Agda module are passed to the `assignCoreNames` function,
-- which will determine the Core name for each module-level Agda name.
--
-- At the moment, auto-generated names are used for all identifiers. Manual
-- forcing of a Core name is possible, but currently not used.
--
-- We also try to incorporate the original Agda name into the generated name
-- as far as possible.
--

module Agda.Compiler.UHC.Naming
  ( NameMap (..) -- we have to export the constructor for the EmbPrj instance in Typechecking/Serialise.
  , AgdaName (..)
  , CoreName (..)
  , EntityType (..)
  , assignCoreNames

  , qnameToCoreName
  , mnameToCoreName
  , getNameMappingFor

  , FreshNameT
  , evalFreshNameT
  , freshLocalName
  )
where

import Data.Char
import Data.List
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative
import Data.Monoid
import Data.Typeable (Typeable)

import Agda.Syntax.Abstract.Name
import Agda.TypeChecking.Monad

import Agda.Compiler.UHC.Bridge

#include "undefined.h"
import Agda.Utils.Impossible

data EntityType
  = EtDatatype
  | EtConstructor
  | EtFunction
  deriving (Eq, Ord, Show, Typeable)

data AgdaName
  = AgdaName
  { anName :: QName
  , anType :: EntityType
  , anNeedsAgdaExport :: Bool       -- ^ If true, this item needs to be exported on the Agda level.
  , anForceName :: Maybe HsName     -- ^ Forces use of the given name.
  }
  deriving (Eq, Ord, Show)

data CoreName
  = CoreName
  { cnName :: HsName        -- ^ The Core name.
  , cnType :: EntityType
  , cnAgdaExported :: Bool  -- ^ True if the name is exported on the Agda level.
  }
  deriving (Show, Typeable)

-- | Contains the mapping between Agda and Core names.
--
-- The mapping is authorative for functions. For constructors and datatypes,
-- you must consult the constructor mapping instead (see ModuleInfo).
--
-- (We still assign core names here for normal constructors/datatypes, but builtin/foreign
-- datatypes/constructors are not always present in the naming db)
data NameMap
  = NameMap
  { entMapping :: M.Map QName CoreName -- ^ maps entities (functions, datatypes, constructors)
  , modMapping :: M.Map ModuleName ([String], HsName) -- we need the string representation to
    -- compute the correct module file name. Maybe we could extract this from the HsName?
  }
  deriving (Show, Typeable)

instance Monoid NameMap where
  mempty = NameMap M.empty M.empty
  mappend x y = NameMap
        { entMapping = entMapping x `M.union` entMapping y
        , modMapping = modMapping x `M.union` modMapping y
        }

type AssignM = StateT AssignState

data AssignState
  = AssignState
  { asNextIdent :: Integer
  , asAgdaModuleName :: ModuleName
  , asCoreModuleName :: [String]
  }

-- | Assign core names for module-level declarations.
assignCoreNames :: MonadTCM m
    => ModuleName    -- ^ Module name.
    -> [AgdaName]           -- ^ Names of all entities, fully qualified.
    -> m NameMap
assignCoreNames modNm ans = do
  nmMp <- evalStateT (do

    -- let's compute the module name
    -- All agda modules live in their own namespace in Agda.XXX, to avoid
    -- clashes with existing haskell modules. (e.g. Data.List) with confusing error messages.
    -- If we don't wan't this, we would have to avoid loading the HS base libraries
    -- or would need package-specific imports. As we don't have this in UHC right now,
    -- this is the best we can do.
    let crModNm = "Agda" : (map show $ mnameToList modNm)
    modify (\x -> x {asCoreModuleName = crModNm} )

    -- functions can only clash between themselves, the same goes for datatypes and constructors.
    -- So we don't have to worry about clashes between entities of a different type.
    -- (because we are in a Haskell-like naming system)

    funs' <- zip funs <$> mapM assignNameProper funs

    dts' <- zip dts <$> mapM assignNameProper dts

    cons' <- zip cons <$> mapM assignNameProper cons

    let entMp = M.fromList [(anName anm, cnm) | (anm, cnm) <- (funs' ++ dts' ++ cons')]
        modMp = M.singleton modNm (crModNm, mkHsName (init crModNm) (last crModNm))
    return $ NameMap entMp modMp
    ) (AssignState 0 modNm __IMPOSSIBLE__)

  reportSLn "uhc.naming" 20 $ "Naming database:\n" ++ show nmMp
  return nmMp
  where etyMp = M.unionsWith (++) [M.singleton (anType a) [a] | a <- ans]
        dts  = M.findWithDefault [] EtDatatype etyMp
        cons = M.findWithDefault [] EtConstructor etyMp
        funs = M.findWithDefault [] EtFunction etyMp



qnameToCoreName :: NameMap -> QName -> Maybe CoreName
qnameToCoreName nmMp qnm = qnm `M.lookup` (entMapping nmMp)

mnameToCoreName :: NameMap -> ModuleName -> Maybe ([String], HsName)
mnameToCoreName nmMp mnm = mnm `M.lookup` (modMapping nmMp)

-- | Returns all names of the given type defined in the given `NameMap`.
getNameMappingFor :: NameMap -> EntityType -> M.Map QName CoreName
getNameMappingFor nmMp ty = M.filter ((ty ==) . cnType) $ entMapping nmMp

-- | Assigns the proper names for entities.
assignNameProper :: (Monad m, Functor m) => AgdaName -> AssignM m CoreName
assignNameProper anm = do
  nm <- case anForceName anm of
    (Just x) -> return x
    Nothing -> freshCrName anm

  return $ CoreName { cnName = nm
                    , cnType = anType anm
                    , cnAgdaExported = anNeedsAgdaExport anm
                    }

-- | Creates a unique fresh core name.
freshCrName :: (Functor m, Monad m) => AgdaName -> AssignM m HsName
freshCrName anm = do
  i <- gets asNextIdent
  modify (\s -> s { asNextIdent = i + 1 } )

  -- we don't really care about the original name, we just keep it for easier debugging
  locName <- either id id <$> unqualifyQ (anName anm)

  modS <- gets asCoreModuleName

  let identName = ("gen_mod_" ++ show i):(map show locName)

  return $ mkUniqueHsName "nl.uu.agda.gen.module" modS (localCrIdent (anType anm) identName)

-- | Sanitizes a name, so that it may be used as a local name on the Core level.
localCrIdent :: EntityType -> [String] -> String
localCrIdent et as =
  case et of
    EtDatatype -> capitalize ns
    EtConstructor -> capitalize ns
    EtFunction -> ((toLower $ head ns):(tail ns))
  where ns = intercalate "_" as
        capitalize (x:xs) = (toUpper x):xs
        capitalize _      = __IMPOSSIBLE__

-- | Returns the names inside a QName, with the module prefix stripped away.
-- If the name is not module-qualified, returns the full name as left. (TODO investigate when this happens)
unqualifyQ :: Monad m => QName -> AssignM m (Either [Name] [Name])
unqualifyQ qnm = do
  amod <- gets asAgdaModuleName
  let modNs = mnameToList amod
      qnms = qnameToList qnm
  case stripPrefix modNs qnms of
    -- not sure when the name doesn't have a module prefix... just force generation of a name for the time being
    Nothing -> return $ Left qnms
    Just nm -> return $ Right nm

------------------------------------
---- local fresh names
------------------------------------

newtype FreshNameT m a = FreshNameT
  { unFreshNameT :: StateT FreshNameState m a}
  deriving (Monad, MonadTrans, Functor, MonadFix, MonadPlus, MonadIO, Applicative, Alternative)

data FreshNameState
  = FreshNameState
  { fnNameSupply :: Integer
  , fnPrefix :: String    -- prefix to use
  }


evalFreshNameT :: Monad m
    => String    -- ^ The name prefix to use.
    -> FreshNameT m a
    -> m a
evalFreshNameT prefix comp = evalStateT (unFreshNameT comp) (FreshNameState 0 prefix)

freshLocalName :: Monad m => FreshNameT m HsName
freshLocalName = FreshNameT $ do
    i <- gets fnNameSupply
    prefix' <- gets fnPrefix
    modify (\s -> s { fnNameSupply = i + 1 } )
    return $ mkUniqueHsName prefix' [] ("gen_loc_" ++ show i)

instance MonadReader s m => MonadReader s (FreshNameT m) where
  ask = lift ask
  local f (FreshNameT x) = FreshNameT $ local f x

instance MonadState s m => MonadState s (FreshNameT m) where
  get = lift get
  put = lift . put

instance (MonadTCM tcm) => MonadTCM (FreshNameT tcm) where
  liftTCM = lift . liftTCM
