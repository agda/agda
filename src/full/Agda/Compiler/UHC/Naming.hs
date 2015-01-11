{-# LANGUAGE CPP, DoAndIfThenElse, DeriveDataTypeable #-}
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
-- The strategy is to "haskellify" all names. This may lead to clashes
-- between multiple entities. The assignCoreNames may assign arbitrary
-- Core names to Agda identifiers, and may also choose to not export
-- entities on the Core level if the anCoreExport is not set to required.
--
-- Invariants:
-- - If an Agda name is marked as Agda exported, the created Core name will always be exported on the Agda level.
-- - If an Agda name is marked as requiring Core export, the created Core name will always be export on the Core
--   level (or a type error will be emitted).

module Agda.Compiler.UHC.Naming
  ( NameMap (..) -- we have to export the constructor for the EmbPrj instance in Typechecking/Serialise.
  , AgdaName (..)
  , CoreName (..)
  , EntityType (..)
  , AgdaCoreExport (..)
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
import Control.Applicative
import Data.Monoid
import Data.Typeable (Typeable)

import Agda.Syntax.Abstract.Name
import Agda.TypeChecking.Monad

import UHC.Light.Compiler.Core.API

#include "undefined.h"
import Agda.Utils.Impossible

data EntityType
  = EtDatatype
  | EtConstructor
  | EtFunction
  deriving (Eq, Ord, Show, Typeable)

data AgdaCoreExport
  = AceNo       -- ^ Don't export.
  | AceWanted   -- ^ Export if possible, but not required.
  | AceRequired -- ^ Export, fail if not possible.
  deriving (Eq, Ord, Show)

data AgdaName
  = AgdaName
  { anName :: QName
  , anType :: EntityType
  , anNeedsAgdaExport :: Bool       -- ^ If true, this item needs to be exported on the Agda level.
  , anCoreExport :: AgdaCoreExport  -- ^ If true, this item wants to be exported on the Core level.
  , anForceName :: Maybe HsName     -- ^ Forces use of the given name.
  }
  deriving (Eq, Ord, Show)

data CoreName
  = CoreName
  { cnName :: HsName        -- ^ The Core name.
  , cnType :: EntityType
  , cnAgdaExported :: Bool  -- ^ True if the name is exported on the Agda level.
  , cnCoreExported :: Bool  -- ^ True if the name is exported on the Core level.
  }
  deriving (Show, Typeable)

-- | Contains the mapping between Agda and Core names.
--
-- The mapping is authorative for functions. For constructors and datatypes,
-- you must consult the constructor mapping instead (see ModuleInfo).
--
-- (We sitll assign core names here for normal constructors/datatypes, but builtin/foreign
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
    
    -- First, do the functions, try drop clashing ones
    funs' <- zip funs <$> mapM assignNameProper funs
    funs'' <- resolveClashes handlerDropExport funs'

    dts' <- zip dts <$> mapM assignNameProper dts
    dts'' <- resolveClashes handlerDropExport dts'

    -- we could also resort to prefixing constructor with the datatype names, would that be a good idea?
    cons' <- zip cons <$> mapM assignNameProper cons
    cons'' <- resolveClashes handlerDropExport cons'
    
    let entMp = M.fromList [(anName anm, cnm) | (anm, cnm) <- (funs'' ++ dts'' ++ cons'')]
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


-- | Resolves name clases between core names. The returned result is free from clashes.
resolveClashes :: MonadTCM m
  => ((HsName, [(AgdaName, CoreName)]) -> AssignM TCM [(AgdaName, CoreName)])   -- ^ Clash handler. Given the clashing entities,
                                                                            -- produce new core names which do not clash.
  -> [(AgdaName, CoreName)] -- ^ The initial names.
  -> AssignM m [(AgdaName, CoreName)]
resolveClashes handler nms =
  -- repeat untilt there is no longer any clash. (TODO how do we guarantuee termination??)
  if M.null clashes then return nms else (updNames >>= resolveClashes handler)
  where (ok, clashes) = findClashes nms
        -- use ok part, and add handled entities
        updNames = (ok ++) . concat <$> mapM handlerDropExport (M.toList clashes)

findClashes :: [(AgdaName, CoreName)]
    -> ([(AgdaName, CoreName)], M.Map HsName [(AgdaName, CoreName)]) -- ^ First item are the non-clashing names, second item are the clashing names.
findClashes nms = (concat $ M.elems ok, clashes)
  where crNmMp = M.unionsWith (++) [M.singleton (cnName cnm) [nm] | nm@(anm, cnm) <- nms]
        (ok, clashes) = M.partition ((<= 1) . length) crNmMp

handlerDropExport :: MonadTCM m => (HsName, [(AgdaName, CoreName)]) -> AssignM m [(AgdaName, CoreName)]
handlerDropExport (crNm, clashes) = do
  -- first, set all aceWanted to not export, then see if there is still a clash
  firstStage <- mapM (\(anm, crm) -> case anForceName anm of
        Just x -> return (anm, crm) -- has forced name, can't change it
        Nothing -> case anCoreExport anm of
                    AceNo -> __IMPOSSIBLE__ -- automatic names cannot clash...
                    AceWanted -> do
                        fnm <- freshCrName anm
                        return (anm, crm { cnName = fnm, cnCoreExported = False })
                    AceRequired -> return (anm,crm)) clashes

  -- now, check if there are still clashes in the aceRequired items
  let (_, clashes') = findClashes firstStage

  let showEnts = (\clsh -> intercalate ", " $ map (show . anName . fst) clsh) 

  if M.null clashes' then do
    lift $ reportSLn "uhc" 10 $
        "Not exporting some entities due to clashing Core names (" ++ show crNm ++ "), entities: " ++ showEnts clashes
    return firstStage
  else do
    -- clashes should have exactly one item at key crNm now
    lift $ typeError $ GenericError $ 
        "The generated Core name (" ++ show crNm ++ ") for the following entities clash: " ++ showEnts (clashes' M.! crNm)

-- | Assigns the proper names for entities. There might be
-- name clashes in the generated names, which will be recitified by 'resolveClashes'.
assignNameProper :: (Monad m, Functor m) => AgdaName -> AssignM m CoreName
assignNameProper anm = do
  nm <- case anForceName anm of
    (Just x) -> return x
    Nothing -> case anCoreExport anm of
            AceNo -> freshCrName anm
            -- TODO either remove this part, or make it work. Just disabled for now,
            -- to make everything else work.
            AceWanted -> __IMPOSSIBLE__
            AceRequired -> __IMPOSSIBLE__

  return $ CoreName { cnName = nm
                    , cnType = anType anm
                    , cnAgdaExported = anNeedsAgdaExport anm
                    , cnCoreExported = anCoreExport anm /= AceNo
                    }
{-  where crHsName = (do
            modS <- map show . mnameToList <$> gets asAgdaModuleName
            locName <- map show <$> (unqualifyQ $ anName anm)
            return $ mkHsName modS (localCrIdent (anType anm) locName)
            )-}

-- | Creates a unique fresh core name. (not core exportable)
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
  mod <- gets asAgdaModuleName
  let modNs = mnameToList mod 
      qnms = qnameToList qnm
  case stripPrefix modNs qnms of
    -- not sure when the name doesn't have a module prefix... just force generation of a name for the time being
    Nothing -> return $ Left qnms
    Just nm -> return $ Right nm

------------------------------------
---- local fresh names
------------------------------------

type FreshNameT = StateT FreshNameState

data FreshNameState
  = FreshNameState
  { nameSupply :: Integer
  , prefix :: String    -- prefix to use
  }

evalFreshNameT :: Monad m
    => String    -- ^ The name prefix to use.
    -> FreshNameT m a
    -> m a
evalFreshNameT prefix comp = evalStateT comp (FreshNameState 0 prefix)

-- | Create a new local identifier (e.g. lambda parameter). 
freshLocalName :: Monad m => FreshNameT m HsName
freshLocalName = do 
  i <- gets nameSupply
  prefix' <- gets prefix
  modify (\s -> s { nameSupply = i + 1 } )
  return $ mkUniqueHsName prefix' [] ("gen_loc_" ++ show i) 

-- | Create a new local identifier (e.g. lambda parameter). Tries to incorporate
-- the given name into the new one, but this is not guarantueed.
--freshLocalName1 :: Monad m => FreshNameM m HsName
