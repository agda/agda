{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE UndecidableInstances       #-}

-- | Contains the state monad that the compiler works in and some functions
--   for tampering with the state.
module Agda.Compiler.UHC.CompileState
  ( CompileT
  , Compile
  , runCompileT

  , addExports
  , addMetaCon
  , addMetaData
  , getExports
  , getDeclMetas

  , getCoreName
  , getCoreName1
  , getConstrCTag
  , getConstrFun
  , moduleNameToCoreName
  , moduleNameToCoreNameParts
  , freshLocalName

  , getCurrentModule

  , conArityAndPars
  , dataRecCons
  )
where

import Control.Monad.State
import Control.Monad.Reader.Class
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Char

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative
import Data.Monoid
#endif

import Agda.Compiler.UHC.ModuleInfo
import Agda.Compiler.UHC.MagicTypes
import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Monad.Builtin hiding (coinductionKit')
import qualified Agda.TypeChecking.Monad as TM
import Agda.Compiler.UHC.Bridge
import Agda.Compiler.UHC.Pragmas.Base

import Agda.Utils.Lens

#include "undefined.h"
import Agda.Utils.Impossible

import Data.Time.Clock.POSIX

getTime :: IO Integer
getTime = round <$> getPOSIXTime

-- | Stuff we need in our compiler
data CompileState = CompileState
    { curModule       :: ModuleName
    , coreMetaData :: Map.Map QName ( [CDataCon] -> CDeclMeta )
    , coreMetaCon :: Map.Map QName [CDataCon] -- map data name to constructors
    , coreExports :: [CExport] -- ^ UHC core exports
    , nameSupply :: Integer
    }

-- | Compiler monad
newtype CompileT m a = CompileT { unCompileT :: StateT CompileState m a }
  deriving (Monad, MonadIO, MonadTrans, Applicative, Functor)

type Compile = CompileT TCM

-- | Used to run the Agda-to-UHC Core transformation.
-- During this transformation,
runCompileT :: MonadIO m =>
       ModuleName   -- ^ The module to compile.
    -> [AModuleInfo] -- ^ Imported module info, non-transitive.
    -> CompileT m a
    -> m (a, AModuleInfo)
runCompileT amod curImpMods comp = do
  (result, state') <- runStateT (unCompileT comp) initial

  version <- liftIO getTime

  let modInfo = AModuleInfo
        { amiFileVersion = currentModInfoVersion
        , amiModule = amod
        , amiVersion = version
        , amiDepsVersion = [ (amiModule m, amiVersion m) |  m <- curImpMods]
        }

  return (result, modInfo)
  where initial = CompileState
            { curModule     = amod
            , coreMetaData = Map.empty
            , coreMetaCon = Map.empty
            , coreExports = []
            , nameSupply = 0
            }

addExports :: Monad m => [HsName] -> CompileT m ()
addExports = addExports' . map mkExport

addExports' :: Monad m => [CExport] -> CompileT m ()
addExports' nms =
  CompileT $ modify (\s -> s { coreExports = nms ++ (coreExports s) } )

addMetaCon :: QName -> CDataCon -> Compile ()
addMetaCon q c = do
  dtNm <- conData . theDef <$> lift (getConstInfo q)
  CompileT $ modify (\s -> s { coreMetaCon = Map.insertWith (++) dtNm [c] (coreMetaCon s) } )

addMetaData :: QName -> ([CDataCon] -> CDeclMeta) -> Compile ()
addMetaData q d =
  CompileT $ modify (\s -> s {coreMetaData = Map.insert q d (coreMetaData s) } )

getExports :: Monad m => CompileT m [CExport]
getExports = CompileT $ gets coreExports

getDeclMetas :: Monad m => CompileT m [CDeclMeta]
getDeclMetas = CompileT $ do
  cons <- gets coreMetaCon
  dts <- gets coreMetaData
  return $ map (\(dtNm, f) -> f (Map.findWithDefault [] dtNm cons)) (Map.toList dts)


getCurrentModule :: Monad m => CompileT m ModuleName
getCurrentModule = CompileT $ gets curModule

freshLocalName :: Monad m => CompileT m HsName
freshLocalName = CompileT $ do
    i <- gets nameSupply
    modify (\s -> s { nameSupply = i + 1 } )
    return $ mkUniqueHsName "nl.uu.agda.fresh-local-name" [] ("x" ++ show i)

-----------------
-- Constructors
-----------------


-- | Copy pasted from MAlonzo....
--   Move somewhere else!
conArityAndPars :: QName -> TCM (Nat, Nat)
conArityAndPars q = do
  def <- getConstInfo q
  TelV tel _ <- telView $ defType def
  let Constructor{ conPars = np } = theDef def
      n = genericLength (telToList tel)
  return (n - np, np)

-- | Returns the CTag for a constructor. Not defined
-- for Sharp and magic __UNIT__ constructor.
getConstrCTag :: QName -> Compile CTag
getConstrCTag q = do
  def <- lift $ getConstInfo q
  (arity, _) <- lift $ conArityAndPars q
  case compiledCore $ defCompiledRep def of
    Nothing -> do
      let dtQ = conData $ theDef def
      -- get tag, which is the index of current con in datatype con list
      tag <- fromJust . elemIndex q . dataRecCons . theDef <$> lift (getConstInfo dtQ)
      mkCTag <$> getCoreName dtQ <*> (getCoreName q) <*> pure tag <*> pure arity
    Just (CrConstr crCon) -> do
      return $ coreConstrToCTag crCon arity
    _ -> __IMPOSSIBLE__


-- | Returns the expression to use to build a value of the given datatype/constructor.
getConstrFun :: QName -> Compile HsName
getConstrFun q = do
  def <- lift $ getConstInfo q
  case compiledCore $ defCompiledRep def of
    Nothing -> getCoreName q
    Just (CrConstr crCon) ->
      return $
        destructCTag builtinUnitCtor (\_ con _ _ -> con)
          (coreConstrToCTag crCon 0) -- Arity doesn't matter here, as we immediately destruct the ctag again!
    _ -> __IMPOSSIBLE__

dataRecCons :: Defn -> [QName]
dataRecCons r@(Record{}) = [recCon r]
dataRecCons d@(Datatype{}) = dataCons d
dataRecCons _ = __IMPOSSIBLE__


-----------------
-- Names
-----------------

-- All agda modules live in their own namespace in Agda.XXX, to avoid
-- clashes with existing haskell modules. (e.g. Data.List) with confusing error messages.
-- If we don't wan't this, we would have to avoid loading the HS base libraries
-- or would need package-specific imports. As we don't have this in UHC right now,
-- this is the best we can do.
moduleNameToCoreNameParts :: ModuleName -> [String]
moduleNameToCoreNameParts modNm = "Agda" : (map show $ mnameToList modNm)

moduleNameToCoreName :: ModuleName -> HsName
moduleNameToCoreName modNm = mkHsName (init nmParts) (last nmParts)
  where nmParts = moduleNameToCoreNameParts modNm

getCoreName :: QName -> Compile HsName
getCoreName qnm = CompileT $ do
  lift $ getCoreName1 qnm

getCoreName1 :: QName -> TCM HsName
getCoreName1 qnm = do

  modNm <- topLevelModuleName qnm

  def <- theDef <$> getConstInfo qnm

  let locName = intercalate "_" $ map show $ either id id $ unqualifyQ modNm qnm
      modParts = moduleNameToCoreNameParts modNm
      identName = locName ++ "_" ++ show idnum
      identName' = case def of
        Datatype{} -> capitalize identName
        Record{} -> capitalize identName
        Constructor{} -> capitalize identName
        _ -> identName

  return $ mkUniqueHsName "nl.uu.agda.top-level-def" modParts identName
  where
    idnum = let (NameId x _) = nameId $ qnameName qnm in x
    -- we don't really care about the original name, we just keep it for easier debugging
    capitalize (x:xs) = (toUpper x):xs
    capitalize _      = __IMPOSSIBLE__

topLevelModuleName :: QName -> TCM ModuleName
topLevelModuleName qnm = go (qnameModule qnm)
  where
    go :: ModuleName -> TCM ModuleName
    go mnm = do
      topMods <- use stModuleToSource
      if (toTopLevelModuleName mnm) `Map.member` topMods
        then return mnm
        else go (mnameFromList $ init $ mnameToList mnm)

-- | Returns the names inside a QName, with the module prefix stripped away.
-- If the name is not module-qualified, returns the full name as left. (TODO investigate when this happens)
unqualifyQ :: ModuleName -> QName -> Either [Name] [Name]
unqualifyQ modNm qnm =
  case stripPrefix modNs qnms of
    -- not sure when the name doesn't have a module prefix... just force generation of a name for the time being
    Nothing -> Left qnms
    Just nm -> Right nm
  where
    modNs = mnameToList modNm
    qnms = qnameToList qnm




instance MonadReader r m => MonadReader r (CompileT m) where
  ask = lift ask
  local f (CompileT x) = CompileT $ local f x

instance MonadState s m => MonadState s (CompileT m) where
  get = lift get
  put = lift . put

instance MonadTCM m => MonadTCM (CompileT m) where
  liftTCM = lift . TM.liftTCM
