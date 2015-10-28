module Agda.TypeChecking.DefinitionalEquality where

import Data.Monoid

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad

import Agda.Utils.Except

type DefEqM = ExceptT Blocked_ (WriterT All ReduceM)

liftRed :: ReduceM a -> DefEqM a
liftRed = lift . lift

class DefEq t a | a -> t where
  defEq  :: t -> a -> a -> DefEqM (t,a,a)

instance DefEq Type Term where
  defEq t a b =
