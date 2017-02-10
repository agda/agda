{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances       #-}

-- | Contains the state monad that the compiler works in and some functions
--   for tampering with the state.
module Agda.Compiler.UHC.CompileState
  ( CompileT
  , Compile
  , runCompileT
  , lift1
  , CoreMeta

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
import Data.Traversable (traverse)

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative
#endif
import Data.Semigroup (Semigroup, Monoid, (<>), mempty, mappend)

import Agda.Compiler.UHC.MagicTypes
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Monad.Builtin hiding (coinductionKit')
import qualified Agda.TypeChecking.Monad as TM
import Agda.Compiler.UHC.Bridge
import Agda.Compiler.UHC.Pragmas.Base
import Agda.Compiler.UHC.Pragmas.Parse
import Agda.Compiler.Common

import Agda.Compiler.MAlonzo.HaskellTypes (checkConstructorCount)

import Agda.Utils.Lens
import Agda.Utils.Pretty hiding ((<>))

#include "undefined.h"
import Agda.Utils.Impossible

import Data.Time.Clock.POSIX

getTime :: IO Integer
getTime = round <$> getPOSIXTime

data CoreMeta = CoreMeta
  { coreMetaData :: Map.Map QName ( [CDataCon] -> CDeclMeta )
  , coreMetaCon :: Map.Map QName [CDataCon] -- map data name to constructors
  , coreExports :: [CExport] -- ^ UHC core exports
  }

instance Semigroup CoreMeta where
  CoreMeta a b c <> CoreMeta r s t =
    CoreMeta (Map.union a r) (Map.unionWith (++) b s) (c ++ t)

instance Monoid CoreMeta where
  mempty = CoreMeta mempty mempty []
  mappend = (<>)

-- | Stuff we need in our compiler
data CompileState = CompileState
  { coreMeta :: CoreMeta
  , nameSupply :: Integer
  , coreConstructors :: Map.Map QName CoreConstr
    -- ^ This keeps a cache of 'CoreConstr's for constructors. The reason for
    --   this is that COMPILED pragmas are no longer parsed and stored in
    --   interfaces, so we have to reparse pragmas for imported modules. The
    --   cache means we only have to do it once per module instead of once per
    --   constructor use. An alternative would be to have a separate uhc
    --   interface file where we stored parsed pragmas, but parsing should be
    --   fast enough that this isn't a problem.
  }

-- | Compiler monad
newtype CompileT m a = CompileT { unCompileT :: StateT CompileState m a }
  deriving (Monad, MonadIO, MonadTrans, Applicative, Functor)

type Compile = CompileT TCM

-- | Used to run the Agda-to-UHC Core transformation.
-- During this transformation,
runCompileT :: MonadIO m =>
       ModuleName   -- ^ The module to compile.
    -> CompileT m a
    -> m a
runCompileT amod comp = do
  (result, state') <- runStateT (unCompileT comp) initial

  return result
  where initial = CompileState
            { coreMeta = mempty
            , nameSupply = 0
            , coreConstructors = Map.empty
            }

lift1 :: Monad m => (forall a. m a -> m a) -> CompileT m a -> CompileT m a
lift1 f (CompileT m) = CompileT $ StateT $ \ s -> f (runStateT m s)

appendCoreMeta :: Monad m => CoreMeta -> CompileT m ()
appendCoreMeta cm =
  CompileT $ modify (\s -> s { coreMeta = cm `mappend` coreMeta s })

addExports :: Monad m => [HsName] -> CompileT m ()
addExports = addExports' . map mkExport

addExports' :: Monad m => [CExport] -> CompileT m ()
addExports' nms = appendCoreMeta (mempty { coreExports = nms })

addMetaCon :: QName -> CDataCon -> Compile ()
addMetaCon q c = do
  dtNm <- conData . theDef <$> lift (getConstInfo q)
  appendCoreMeta (mempty { coreMetaCon = Map.singleton dtNm [c] })

addMetaData :: QName -> ([CDataCon] -> CDeclMeta) -> Compile ()
addMetaData q d =
  appendCoreMeta (mempty { coreMetaData = Map.singleton q d })

setCoreCon :: QName -> CoreConstr -> Compile ()
setCoreCon c cc = CompileT $ modify $ \ s -> s { coreConstructors = Map.insert c cc $ coreConstructors s }

getCachedCoreCon :: QName -> Compile (Maybe CoreConstr)
getCachedCoreCon c = CompileT $ gets $ Map.lookup c . coreConstructors

getCoreCon :: QName -> Compile CoreConstr
getCoreCon c = do
  mcc <- getCachedCoreCon c
  case mcc of
    Just cc -> return cc
    Nothing -> do -- compute CoreConstr for all constructors of the datatype and cache the result
      cDef@Constructor{ conData = dtQ } <- lift $ theDef <$> getConstInfo c
      dDef <- lift $ getConstInfo dtQ
      let cs = defConstructors $ theDef dDef
      when (null cs) __IMPOSSIBLE__
      dtCr <- getCorePragma dtQ
      case dtCr of
        -- not COMPILED
        Nothing -> do
          let addCon tag q = setCoreCon q =<< CCNormal <$> getCoreName dtQ <*> getCoreName q <*> pure tag
          zipWithM_ addCon [0..] cs
        -- COMPILED type. In this case we parse the COMPILED pragmas again
        -- (although caching ensures only once per module). This should be
        -- cheap but one might consider writing this information to a special
        -- uhc interface file.
        Just (CrData r ct ccrs) -> lift1 (setCurrentRange r) $ do
          lift $ checkConstructorCount dtQ (dataCons $ theDef dDef) ccrs  -- borrowed from GHC backend
          ct <- parseCoreData ct
          ccrs <- parseCoreConstrs ct ccrs
          zipWithM_ setCoreCon cs ccrs
        Just{} -> __IMPOSSIBLE__
      Just cc <- getCachedCoreCon c  -- it's now cached, so we get Just here
      return cc

getExports :: Compile [CExport]
getExports = CompileT $ gets (coreExports . coreMeta)

getDeclMetas :: Compile [CDeclMeta]
getDeclMetas = CompileT $ do
  cons <- gets (coreMetaCon . coreMeta)
  dts <- gets (coreMetaData . coreMeta)
  return $ map (\(dtNm, f) -> f (Map.findWithDefault [] dtNm cons)) (Map.toList dts)

freshLocalName :: Monad m => CompileT m HsName
freshLocalName = CompileT $ do
    i <- gets nameSupply
    modify (\s -> s { nameSupply = i + 1 } )
    return $ mkUniqueHsName "nl.uu.agda.fresh-local-name" [] ("x" ++ show i)

-----------------
-- Constructors
-----------------


-- | Returns the CTag for a constructor. Not defined
-- for Sharp and magic __UNIT__ constructor.
getConstrCTag :: QName -> Compile CTag
getConstrCTag q = do
  def <- lift $ getConstInfo q
  (arity, _) <- lift $ conArityAndPars q
  crCon <- getCoreCon q
  return $ coreConstrToCTag crCon arity


-- | Returns the expression to use to build a value of the given datatype/constructor.
getConstrFun :: QName -> Compile HsName
getConstrFun q = do
  def <- lift $ theDef <$> getConstInfo q
  cc  <- getCoreCon q
  case def of
    Constructor{} -> do
      crCon <- getCoreCon q
      return $
        destructCTag builtinUnitCtor (\_ con _ _ -> con)
          (coreConstrToCTag crCon 0) -- Arity doesn't matter here, as we immediately destruct the ctag again!
    _ -> getCoreName q

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

  modNm <- topLevelModuleName (qnameModule qnm)

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
