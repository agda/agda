{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Agda.TypeChecking.Reduce.Monad where

import Control.Applicative
import Control.Monad.Reader

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad ( TCM, Closure, Definition, Simplification, Reduced, MaybeReducedArgs, PrimFun, MetaVariable
                               , AllowedReductions, TCEnv)
import qualified Agda.TypeChecking.Monad as TCM
import qualified Agda.TypeChecking.EtaContract as TCM
import qualified Agda.TypeChecking.Monad.Builtin as TCM
import Agda.TypeChecking.Substitute
import Agda.Utils.Pretty

newtype ReduceM a = ReduceM { runReduce :: TCM a }
  deriving (Functor, Applicative, Monad, MonadReader TCEnv, TCM.HasOptions)

enterClosure :: Closure a -> (a -> ReduceM b) -> ReduceM b
enterClosure cl f = ReduceM $ TCM.enterClosure cl (runReduce . f)

underAbstraction_ :: Subst a => Abs a -> (a -> ReduceM b) -> ReduceM b
underAbstraction_ a f = ReduceM $ TCM.underAbstraction_ a (runReduce . f)

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

-- TODO: this won't work
primFunImplementation :: PrimFun -> [Arg Term] -> ReduceM (Reduced MaybeReducedArgs Term)
primFunImplementation pf args = ReduceM $ TCM.primFunImplementation pf args

getPrimitive :: String -> ReduceM PrimFun
getPrimitive = ReduceM . TCM.getPrimitive

getBuiltin' :: String -> ReduceM (Maybe Term)
getBuiltin' = ReduceM . TCM.getBuiltin'

lookupMeta :: MetaId -> ReduceM MetaVariable
lookupMeta = ReduceM . TCM.lookupMeta

primZero :: ReduceM Term
primZero = ReduceM TCM.primZero

primSuc :: ReduceM Term
primSuc = ReduceM TCM.primSuc

constructorForm :: Term -> ReduceM Term
constructorForm = TCM.constructorForm' primZero primSuc

