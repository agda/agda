{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Agda.TypeChecking.Reduce.Monad where

import Control.Applicative
import Control.Monad.Reader

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
  (ReduceM(..), TCM, Closure, Definition, Simplification, Reduced,
   MaybeReducedArgs, PrimFun, MetaVariable, AllowedReductions, TCEnv,
   HasOptions(..))
import qualified Agda.TypeChecking.Monad as TCM
import qualified Agda.TypeChecking.EtaContract as TCM
import qualified Agda.TypeChecking.Monad.Builtin as TCM
import Agda.TypeChecking.Substitute
import Agda.Utils.Pretty

instance HasOptions ReduceM where
  pragmaOptions      = ReduceM pragmaOptions
  commandLineOptions = ReduceM commandLineOptions

instance TCM.HasBuiltins ReduceM where
  getBuiltinThing = ReduceM . TCM.getBuiltinThing

constructorForm :: Term -> ReduceM Term
constructorForm v = ReduceM $ TCM.constructorForm v

enterClosure :: Closure a -> (a -> ReduceM b) -> ReduceM b
enterClosure cl f = ReduceM $ TCM.enterClosure cl (runReduceM . f)

underAbstraction_ :: Subst a => Abs a -> (a -> ReduceM b) -> ReduceM b
underAbstraction_ a f = ReduceM $ TCM.underAbstraction_ a (runReduceM . f)

etaOnce :: Term -> ReduceM Term
etaOnce = ReduceM . TCM.etaOnce

isInstantiatedMeta :: MetaId -> ReduceM Bool
isInstantiatedMeta = ReduceM . TCM.isInstantiatedMeta

reportSDoc :: String -> Int -> TCM Doc -> ReduceM ()
reportSDoc t n doc = ReduceM $ TCM.reportSDoc t n doc

reportSLn :: String -> Int -> String -> ReduceM ()
reportSLn t n s = ReduceM $ TCM.reportSLn t n s

getConstInfo :: QName -> ReduceM Definition
getConstInfo = ReduceM . TCM.getConstInfo

typeOfConst :: QName -> ReduceM Type
typeOfConst = ReduceM . TCM.typeOfConst

lookupMeta :: MetaId -> ReduceM MetaVariable
lookupMeta = ReduceM . TCM.lookupMeta

