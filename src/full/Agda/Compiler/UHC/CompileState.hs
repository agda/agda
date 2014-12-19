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
--  , getConstrTag
--  , getConstrArity

  , getCurrentModule

  , constructorArity
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
import Agda.Compiler.UHC.ModuleInfo
import Agda.Interaction.Options
import Agda.Syntax.Internal
import Agda.Syntax.Concrete(TopLevelModuleName)
import Agda.Syntax.Common
import Agda.TypeChecking.Monad (MonadTCM, TCM, internalError, defType, theDef, getConstInfo, sigDefinitions, stImports, stPersistentOptions, stPersistentState)
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
    } deriving Show

-- | Compiler monad
type CompileT = StateT CompileState

-- | The initial (empty) state
runCompileT :: MonadIO m
    => ModuleName   -- ^ The module to compile.
    -> [AModuleInfo] -- ^ Imported module info (non-transitive).
    -> NameMap      -- ^ NameMap for the current module (non-transitive).
    -> CompileT m a
    -> m (a, AModuleInfo)
runCompileT mod impMods nmMp comp = do
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
  where initial = CompileState
            { curModule     = mod
            , moduleInterface   = mappend
                (mempty { amifNameMp = nmMp})
                (mconcat $ map amiInterface impMods)
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
getConstrInfo n = M.findWithDefault __IMPOSSIBLE__ n <$> gets (amifConMp . moduleInterface)


getCurrentModule :: Monad m => CompileT m ModuleName
getCurrentModule = gets curModule

-- TODO What does this have to do with CompileState? Move
replaceAt :: Int -- ^ replace at
          -> [a] -- ^ to replace
          -> [a] -- ^ replace with
          -> [a] -- ^ result?
replaceAt n xs inserts = let (as, _:bs) = splitAt n xs in as ++ inserts ++ bs


-- TODO this has nothing todo with the CompileState.., move
-- | Copy pasted from MAlonzo, then Epic, HAHA!!!
--   Move somewhere else!
constructorArity :: Num a => QName -> TCM a
constructorArity q = do
  def <- getConstInfo q
  a <- normalise $ defType def
  case theDef def of
    TM.Constructor{ TM.conPars = np } -> return . fromIntegral $ arity a - np
    _ -> internalError $ "constructorArity: non constructor: " ++ show q

