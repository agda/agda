{-# OPTIONS_GHC -fno-warn-orphans     #-}
{-# OPTIONS_GHC -fwarn-unused-imports #-}

module Agda.TypeChecking.Serialise.Instances.Compilers where

import qualified Data.Binary.Get as B
import qualified Data.Binary.Put as B

import qualified Agda.Compiler.UHC.Pragmas.Base as CR
import qualified Agda.Compiler.UHC.Bridge as UHCB

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common ()

import Agda.TypeChecking.Monad

instance EmbPrj HaskellRepresentation where
  icod_ (HsType a) = icode1 0 a
  icod_ (HsDefn a) = icode1 1 a

  value = vcase valu where
    valu [0, a] = valu1 HsType a
    valu [1, a] = valu1 HsDefn a
    valu _      = malformed

instance EmbPrj CompiledRepresentation where
  icod_ (CompiledRep a b c d) = icode4' a b c d

  value = vcase valu where
    valu [a, b, c, d] = valu4 CompiledRep a b c d
    valu _            = malformed

instance EmbPrj CoreRepresentation where
  icod_ (CrDefn a)   = icode1 1 a
  icod_ (CrType a)   = icode1 2 a
  icod_ (CrConstr a) = icode1 3 a

  value = vcase valu where
    valu [1, a] = valu1 CrDefn a
    valu [2, a] = valu1 CrType a
    valu [3, a] = valu1 CrConstr a
    valu _      = malformed

instance EmbPrj CR.CoreType where
  icod_ (CR.CTMagic a) = icode1 1 a
  icod_ (CR.CTNormal a)  = icode1 2 a

  value = vcase valu where
    valu [1, a]    = valu1 CR.CTMagic a
    valu [2, a]    = valu1 CR.CTNormal a
    valu _         = malformed

instance EmbPrj CR.CoreConstr where
  icod_ (CR.CCMagic a b)    = icode2 1 a b
  icod_ (CR.CCNormal a b c) = icode3 2 a b c

  value = vcase valu where
    valu [1, a, b]    = valu2 CR.CCMagic a b
    valu [2, a, b, c] = valu3 CR.CCNormal a b c
    valu _            = malformed

instance EmbPrj CR.HsName where
  icod_   = icode . B.runPut . UHCB.serialize
  value n = value n >>= return . (B.runGet UHCB.unserialize)

