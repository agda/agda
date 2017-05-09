{-# OPTIONS_GHC -fno-warn-orphans     #-}
{-# OPTIONS_GHC -fwarn-unused-imports #-}

module Agda.TypeChecking.Serialise.Instances.Compilers where

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common

import Agda.TypeChecking.Monad

instance EmbPrj CompilerPragma where
  icod_ (CompilerPragma a b) = icode2' (SerialisedRange a) b

  value = value2 (CompilerPragma . underlyingRange)

instance EmbPrj ForeignCode where
  icod_ (ForeignCode r a) = icode2' (SerialisedRange r) a

  value = value2 (ForeignCode . underlyingRange)

