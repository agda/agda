{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Contains the state monad that the compiler works in and some functions
--   for tampering with the state.
module Agda.Compiler.UHC.CompileState
  ( CompileT (..) -- we don't really want to export the ctor, but we need it in Transform
  , runCompileT
  , uhcError

  , addConMap

  , getCoreName
  , getCoreName1
  , getConstrInfo
  , getConstrFun
  , isConstrInstantiated
  , getCoinductionKit

  , getCurrentModule

  , conArityAndPars
  , replaceAt

  -- internal use only
  , CompileState (..)
  )
where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader.Class
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import Data.Time.Clock.POSIX

import Agda.Compiler.UHC.AuxAST as AuxAST
import Agda.Compiler.UHC.AuxASTUtil
import Agda.Compiler.UHC.ModuleInfo
import Agda.Compiler.UHC.MagicTypes
import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.TypeChecking.Monad (MonadTCM, TCM, internalError, defType, theDef, getConstInfo)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Monad.Builtin hiding (coinductionKit')
import qualified Agda.TypeChecking.Monad as TM
import Agda.Compiler.UHC.Naming

#include "undefined.h"
import Agda.Utils.Impossible


-- | Stuff we need in our compiler
data CompileState = CompileState
    { curModule       :: ModuleName
    , moduleInterface :: AModuleInterface    -- ^ Contains the interface of all imported and the currently compiling module.
    , curModuleInterface :: AModuleInterface -- ^ Interface of the current module only.
    , coinductionKit' :: Maybe CoinductionKit
    }

-- | Compiler monad
newtype CompileT m a = CompileT { unCompileT :: StateT CompileState m a }
  deriving (Monad, MonadIO, MonadTrans, Applicative, Functor)

-- | Used to run the Agda-to-AuxAST transformation.
-- During this transformation,
runCompileT :: MonadIO m
    => Maybe CoinductionKit
    -> ModuleName   -- ^ The module to compile.
    -> [AModuleInfo] -- ^ Imported module info, non-transitive.
    -> AModuleInterface -- ^ Imported module interface, transitive.
    -> NameMap      -- ^ NameMap for the current module, non-transitive.
    -> ConInstMp
    -> CompileT m a
    -> m (a, AModuleInfo)
runCompileT coind amod curImpMods transImpIface nmMp conIMp comp = do
  (result, state') <- runStateT (unCompileT comp) initial

  version <- liftIO getPOSIXTime

  let modInfo = AModuleInfo
        { amiFileVersion = currentModInfoVersion
        , amiModule = amod
        , amiInterface = curModuleInterface state'
        , amiVersion = version
        , amiDepsVersion = [ (amiModule m, amiVersion m) |  m <- curImpMods]
        }

  return (result, modInfo)
  where initialModIface = mempty { amifNameMp = nmMp, amifConInstMp = conIMp }
        initial = CompileState
            { curModule     = amod
            , moduleInterface =
                initialModIface `mappend` transImpIface
            , curModuleInterface = initialModIface
            , coinductionKit' = coind
            }


-- | Add the given constructor map to the transitive interface, and set it
-- as the constructor map for the current module.
addConMap :: Monad m => M.Map QName AConInfo -> CompileT m ()
addConMap conMp = CompileT $ modify (\s -> s
                    { moduleInterface = (moduleInterface s `mappend` ifaceConMp)
                    , curModuleInterface = ( (curModuleInterface s) { amifConMp = conMp })
                    })
  where ifaceConMp = mempty { amifConMp = conMp }


-- | When normal errors are not enough
uhcError :: MonadTCM m => String -> CompileT m a
uhcError = CompileT . lift . internalError

getCoreName :: Monad m => QName -> CompileT m (Maybe HsName)
getCoreName qnm = CompileT $ do
  nmMp <- gets (amifNameMp . moduleInterface)
  return $ (cnName <$> qnameToCoreName nmMp qnm)

getCoreName1 :: Monad m => QName -> CompileT m HsName
getCoreName1 nm = getCoreName nm >>= return . (fromMaybe __IMPOSSIBLE__)

getConstrInfo :: (Functor m, Monad m) => QName -> CompileT m AConInfo
getConstrInfo n = CompileT $ do
  instMp <- gets (amifConInstMp . moduleInterface)
  let realConNm = M.findWithDefault __IMPOSSIBLE__ n instMp
  M.findWithDefault __IMPOSSIBLE__ realConNm <$> gets (amifConMp . moduleInterface)

isConstrInstantiated :: (Functor m, Monad m) => QName -> CompileT m Bool
isConstrInstantiated n =  CompileT $ ((n /=) . M.findWithDefault __IMPOSSIBLE__ n) <$> gets (amifConInstMp . moduleInterface)

getCoinductionKit :: Monad m => CompileT m (Maybe CoinductionKit)
getCoinductionKit = CompileT $ gets coinductionKit'

getCurrentModule :: Monad m => CompileT m ModuleName
getCurrentModule = CompileT $ gets curModule

-- TODO What does this have to do with CompileState? Move
replaceAt :: Int -- ^ replace at
          -> [a] -- ^ to replace
          -> [a] -- ^ replace with
          -> [a] -- ^ result?
replaceAt n xs inserts = let (as, _:bs) = splitAt n xs in as ++ inserts ++ bs



-- | Copy pasted from MAlonzo....
--   Move somewhere else!
conArityAndPars :: QName -> TCM (Nat, Nat)
conArityAndPars q = do
  def <- getConstInfo q
  TelV tel _ <- telView $ defType def
  let TM.Constructor{ TM.conPars = np } = theDef def
      n = genericLength (telToList tel)
  return (n - np, np)


-- | Returns the expression to use to build a value of the given datatype/constructor.
-- The returned expression may be fully or partially applied.
getConstrFun :: MonadTCM m => QName -> CompileT m HsName
getConstrFun conNm = do
  kit <- getCoinductionKit

  case (Just conNm) == (nameOfSharp <$> kit) of
    True -> getCoreName1 conNm
    False -> do
            -- we can't just use getCoreName here, because foreign constructors
            -- are not part of the name map.
            conInfo <- getConstrInfo conNm
            let conDef = aciDataCon conInfo
                tyDef = aciDataType conInfo

            case xdatImplType tyDef of
              (ADataImplMagic nm) | nm == "UNIT" -> return $ builtinUnitCtor -- already fully applied
              _ -> return $ ctagCtorName $ xconCTag conDef

instance MonadReader r m => MonadReader r (CompileT m) where
  ask = lift ask
  local f (CompileT x) = CompileT $ local f x

instance MonadState s m => MonadState s (CompileT m) where
  get = lift get
  put = lift . put

instance MonadTCM m => MonadTCM (CompileT m) where
  liftTCM = lift . TM.liftTCM
