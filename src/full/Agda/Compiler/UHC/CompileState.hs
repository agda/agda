{-# LANGUAGE CPP #-}

-- | Contains the state monad that the compiler works in and some functions
--   for tampering with the state.
module Agda.Compiler.UHC.CompileState
  ( CompileT
  , runCompileT
  , uhcError

  , addConMap

  , getCoreName
  , getCoreName1
  , getConstrInfo
  , getConstrFun
  , isConstrInstantiated
--  , getConstrTag
--  , getConstrArity
  , getCoinductionKit
  , getBuiltinCache

  , getCurrentModule

  , conArityAndPars
  , replaceAt
  )
where

import Control.Applicative
import Control.Monad.State
import Data.List
import Data.Map(Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import Data.Set(Set)
import qualified Data.Set as S
import Data.Time.Clock.POSIX

import Agda.Compiler.UHC.AuxAST as AuxAST
import Agda.Compiler.UHC.AuxASTUtil
import Agda.Compiler.UHC.ModuleInfo
import Agda.Compiler.UHC.Builtins
import Agda.Interaction.Options
import Agda.Syntax.Internal
import Agda.Syntax.Concrete(TopLevelModuleName)
import Agda.Syntax.Common
import Agda.TypeChecking.Monad (MonadTCM, TCM, internalError, defType, theDef, getConstInfo, sigDefinitions, stImports, stPersistentOptions, stPersistentState)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Monad.Builtin
import qualified Agda.TypeChecking.Monad as TM
import Agda.TypeChecking.Reduce
import Agda.Compiler.UHC.Naming
import Agda.TypeChecking.Serialise (currentInterfaceVersion)

import qualified Agda.Utils.HashMap as HM
import Agda.Utils.Lens

#include "undefined.h"
import Agda.Utils.Impossible


-- | Stuff we need in our compiler
data CompileState = CompileState
    { curModule       :: ModuleName
    , moduleInterface :: AModuleInterface    -- ^ Contains the interface of all imported and the currently compiling module.
    , coinductionKit' :: Maybe CoinductionKit
    , builtins :: BuiltinCache
    }

-- | Compiler monad
type CompileT = StateT CompileState

-- | The initial (empty) state
runCompileT :: MonadIO m
    => Maybe CoinductionKit
    -> BuiltinCache
    -> ModuleName   -- ^ The module to compile.
    -> [AModuleInfo] -- ^ Imported module info (non-transitive).
    -> NameMap      -- ^ NameMap for the current module (non-transitive).
    -> ConInstMp
    -> CompileT m a
    -> m (a, AModuleInfo)
runCompileT coind btins mod impMods nmMp conIMp comp = do
  (result, state') <- runStateT comp initial

  version <- liftIO getPOSIXTime

  let modInfo = AModuleInfo
        { amiFileVersion = currentModInfoVersion
        , amiAgdaVersion = currentInterfaceVersion
        , amiModule = mod
        , amiInterface = moduleInterface state'
        , amiCurNameMp = nmMp
        , amiVersion = version
        , amiDepsVersion = [ (amiModule m, amiVersion m) |  m <- impMods]
        }

  return (result, modInfo)
  where initialModIface = mempty { amifNameMp = nmMp, amifConInstMp = conIMp }
        initial = CompileState
            { curModule     = mod
            , moduleInterface   = mappend
                initialModIface
                (mconcat $ map amiInterface impMods)
            , coinductionKit' = coind
            , builtins = btins
            }

addConMap :: Monad m => M.Map QName AConInfo -> CompileT m ()
addConMap conMp = addInterface (mempty { amifConMp = conMp })

-- | Adds the given interface.
addInterface :: Monad m => AModuleInterface -> CompileT m ()
addInterface iface = modifyInterface (mappend iface)

modifyInterface :: Monad m => (AModuleInterface -> AModuleInterface) -> CompileT m ()
modifyInterface f = modify (\s -> s { moduleInterface = f (moduleInterface s )})



-- | When normal errors are not enough
uhcError :: MonadTCM m => String -> CompileT m a
uhcError = lift . internalError

getCoreName :: Monad m => QName -> CompileT m (Maybe HsName)
getCoreName qnm = do
  nmMp <- gets (amifNameMp . moduleInterface)
  return $ (cnName <$> qnameToCoreName nmMp qnm)

getCoreName1 :: Monad m => QName -> CompileT m HsName
getCoreName1 nm = getCoreName nm >>= return . (fromMaybe __IMPOSSIBLE__)

getConstrInfo :: (Functor m, Monad m) => QName -> CompileT m AConInfo
getConstrInfo n = do
  instMp <- gets (amifConInstMp . moduleInterface)
  M.findWithDefault __IMPOSSIBLE__ (M.findWithDefault (error $ show n) n instMp) <$> gets (amifConMp . moduleInterface)

isConstrInstantiated :: (Functor m, Monad m) => QName -> CompileT m Bool
isConstrInstantiated n =  ((n /=) . M.findWithDefault __IMPOSSIBLE__ n) <$> gets (amifConInstMp . moduleInterface)

getCoinductionKit :: Monad m => CompileT m (Maybe CoinductionKit)
getCoinductionKit = gets coinductionKit'

getCurrentModule :: Monad m => CompileT m ModuleName
getCurrentModule = gets curModule

getBuiltinCache :: Monad m => CompileT m BuiltinCache
getBuiltinCache = gets builtins

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

