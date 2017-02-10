{-# OPTIONS_GHC -fno-warn-orphans     #-}
{-# OPTIONS_GHC -fwarn-unused-imports #-}

module Agda.TypeChecking.Serialise.Instances.Compilers where

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common

import Agda.TypeChecking.Monad

instance EmbPrj CompilerPragma where
  icod_ (CompilerPragma a b) = icode2' (SerialisedRange a) b

  value = vcase valu where
    valu [a, b] = valu2 (CompilerPragma . underlyingRange) a b
    valu _      = malformed

