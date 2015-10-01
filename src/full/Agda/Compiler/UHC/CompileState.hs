{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE UndecidableInstances       #-}

-- | Contains the state monad that the compiler works in and some functions
--   for tampering with the state.
module Agda.Compiler.UHC.CompileState
  ( CompileT (..) -- we don't really want to export the ctor, but we need it in Transform
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
  , getCoinductionKit

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

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative
import Data.Monoid
#endif

import Agda.Compiler.UHC.AuxAST as AuxAST
import Agda.Compiler.UHC.ModuleInfo
import Agda.Compiler.UHC.MagicTypes
import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.TypeChecking.Monad -- (MonadTCM, TCM, internalError, defType, theDef, getConstInfo)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Monad.Builtin hiding (coinductionKit')
import qualified Agda.TypeChecking.Monad as TM
import Agda.Compiler.UHC.Naming
import Agda.Compiler.UHC.Bridge
import Agda.Compiler.UHC.Pragmas.Base

#include "undefined.h"
import Agda.Utils.Impossible

import Data.Time.Clock.POSIX

getTime :: IO Integer
getTime = round <$> getPOSIXTime

-- | Stuff we need in our compiler
data CompileState = CompileState
    { curModule       :: ModuleName
    , moduleInterface :: AModuleInterface    -- ^ Contains the interface of all imported and the currently compiling module.
    , curModuleInterface :: AModuleInterface -- ^ Interface of the current module only.
    , coinductionKit' :: Maybe CoinductionKit
    , coreMetaData :: Map.Map QName ( [CDataCon] -> CDeclMeta )
    , coreMetaCon :: Map.Map QName [CDataCon] -- map data name to constructors
    , coreExports :: [CExport] -- ^ UHC core exports
    }

-- | Compiler monad
newtype CompileT m a = CompileT { unCompileT :: StateT CompileState m a }
  deriving (Monad, MonadIO, MonadTrans, Applicative, Functor)

type Compile = CompileT TCM

-- | Used to run the Agda-to-AuxAST transformation.
-- During this transformation,
runCompileT :: MonadIO m
    => Maybe CoinductionKit
    -> ModuleName   -- ^ The module to compile.
    -> [AModuleInfo] -- ^ Imported module info, non-transitive.
    -> AModuleInterface -- ^ Imported module interface, transitive.
    -> NameMap      -- ^ NameMap for the current module, non-transitive.
    -> CompileT m a
    -> m (a, AModuleInfo)
runCompileT coind amod curImpMods transImpIface nmMp comp = do
  (result, state') <- runStateT (unCompileT comp) initial

  version <- liftIO getTime

  let modInfo = AModuleInfo
        { amiFileVersion = currentModInfoVersion
        , amiModule = amod
        , amiInterface = curModuleInterface state'
        , amiVersion = version
        , amiDepsVersion = [ (amiModule m, amiVersion m) |  m <- curImpMods]
        }

  return (result, modInfo)
  where initialModIface = mempty { amifNameMp = nmMp }
        initial = CompileState
            { curModule     = amod
            , moduleInterface =
                initialModIface `mappend` transImpIface
            , curModuleInterface = initialModIface
            , coinductionKit' = coind
            , coreMetaData = Map.empty
            , coreMetaCon = Map.empty
            , coreExports = []
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

getCoreName :: Monad m => QName -> CompileT m (Maybe HsName)
getCoreName qnm = CompileT $ do
  nmMp <- gets (amifNameMp . moduleInterface)
  return $ (cnName <$> qnameToCoreName nmMp qnm)

getCoreName1 :: Monad m => QName -> CompileT m HsName
getCoreName1 nm = getCoreName nm >>= return . (fromMaybe __IMPOSSIBLE__)

getCoinductionKit :: Monad m => CompileT m (Maybe CoinductionKit)
getCoinductionKit = CompileT $ gets coinductionKit'

getCurrentModule :: Monad m => CompileT m ModuleName
getCurrentModule = CompileT $ gets curModule


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
      nm <- getCoreName1 q
      let dtQ = conData $ theDef def
      -- get tag, which is the index of current con in datatype con list
      tag <- fromJust . elemIndex q . dataRecCons . theDef <$> lift (getConstInfo dtQ)
      mkCTag <$> getCoreName1 dtQ <*> (getCoreName1 q) <*> pure tag <*> pure arity
    Just (CrConstr crCon) -> do
      return $ coreConstrToCTag crCon arity
    _ -> __IMPOSSIBLE__


-- | Returns the expression to use to build a value of the given datatype/constructor.
getConstrFun :: QName -> Compile HsName
getConstrFun q = do
  def <- lift $ getConstInfo q
  case compiledCore $ defCompiledRep def of
    Nothing -> getCoreName1 q
    Just (CrConstr crCon) ->
      return $
        destructCTag builtinUnitCtor (\_ con _ _ -> con)
          (coreConstrToCTag crCon 0) -- Arity doesn't matter here, as we immediately destruct the ctag again!
    _ -> __IMPOSSIBLE__

dataRecCons :: Defn -> [QName]
dataRecCons r@(Record{}) = [recCon r]
dataRecCons d@(Datatype{}) = dataCons d
dataRecCons _ = __IMPOSSIBLE__


instance MonadReader r m => MonadReader r (CompileT m) where
  ask = lift ask
  local f (CompileT x) = CompileT $ local f x

instance MonadState s m => MonadState s (CompileT m) where
  get = lift get
  put = lift . put

instance MonadTCM m => MonadTCM (CompileT m) where
  liftTCM = lift . TM.liftTCM
