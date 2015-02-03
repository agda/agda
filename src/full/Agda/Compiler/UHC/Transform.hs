{-# LANGUAGE CPP #-}

-- | Contains the state monad that the compiler works in and some functions
--   for tampering with the state.
module Agda.Compiler.UHC.Transform
  ( uhcError

  , Transform
  , TransformT
  , runTransformT

  , getCoreName
  , getCoreName1
  , getConstrInfo
  , getConstrFun
  , isConstrInstantiated
--  , getConstrTag
--  , getConstrArity
--  , getCoinductionKit

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
import Agda.Compiler.UHC.CompileState
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

type TransformT = CompileT

type Transform = AMod -> TransformT TCM AMod

runTransformT :: Monad m => AModuleInterface -> ModuleName -> TransformT m a -> m (a, AModuleInterface)
runTransformT iface modNm comp = do
  (result, state) <- runStateT comp initial
  return (result, moduleInterface state)
  where initial = CompileState
            { curModule = modNm
            , moduleInterface = iface
            , coinductionKit' = __IMPOSSIBLE__
            }


