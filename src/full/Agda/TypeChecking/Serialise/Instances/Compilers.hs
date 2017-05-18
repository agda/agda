{-# OPTIONS_GHC -fno-warn-orphans     #-}
{-# OPTIONS_GHC -fwarn-unused-imports #-}

module Agda.TypeChecking.Serialise.Instances.Compilers where

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common

import Agda.TypeChecking.Monad

instance EmbPrj CompilerPragma where
  icod_ (CompilerPragma a b) =
    icodeN' (CompilerPragma . underlyingRange) (SerialisedRange a) b

  value = valueN (CompilerPragma . underlyingRange)

instance EmbPrj ForeignCode where
  icod_ (ForeignCode r a) =
    icodeN' (ForeignCode . underlyingRange) (SerialisedRange r) a

  value = valueN (ForeignCode . underlyingRange)

