{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Serialise.Instances.Abstract where

import Control.Applicative
import qualified Data.Map as Map
import qualified Data.Set as Set

import Agda.Syntax.Common
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Info
import Agda.Syntax.Scope.Base
import Agda.Syntax.Position as P
import Agda.Syntax.Fixity

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common ()

import Agda.TypeChecking.Monad

import Agda.Utils.Except

#include "undefined.h"
import Agda.Utils.Impossible

instance EmbPrj Scope where
  icod_ (Scope a b c d e) = icode5' a b c d e

  value = value5 Scope

instance EmbPrj NameSpaceId where
  icod_ PublicNS        = icode0'
  icod_ PrivateNS       = icode0 1
  icod_ ImportedNS      = icode0 2
  icod_ OnlyQualifiedNS = icode0 3

  value = vcase valu where
    valu []  = valuN PublicNS
    valu [1] = valuN PrivateNS
    valu [2] = valuN ImportedNS
    valu [3] = valuN OnlyQualifiedNS
    valu _   = malformed

instance EmbPrj Access where
  icod_ (PrivateAccess UserWritten) = icode0 0
  icod_ PrivateAccess{} = icode0 1
  icod_ PublicAccess  = icode0'
  icod_ OnlyQualified = icode0 2

  value = vcase valu where
    valu [0] = valuN $ PrivateAccess UserWritten
    valu [1] = valuN $ PrivateAccess Inserted
    valu []  = valuN PublicAccess
    valu [2] = valuN OnlyQualified
    valu _   = malformed

instance EmbPrj NameSpace where
  icod_ (NameSpace a b c) = icode3' a b c

  value = value3 NameSpace

instance EmbPrj WhyInScope where
  icod_ Defined       = icode0'
  icod_ (Opened a b)  = icode2 0 a b
  icod_ (Applied a b) = icode2 1 a b

  value = vcase valu where
    valu []        = valuN Defined
    valu [0, a, b] = valuN Opened a b
    valu [1, a, b] = valuN Applied a b
    valu _         = malformed

instance EmbPrj AbstractName where
  icod_ (AbsName a b c) = icode3' a b c

  value = value3 AbsName

instance EmbPrj AbstractModule where
  icod_ (AbsModule a b) = icode2' a b

  value = value2 AbsModule

instance EmbPrj KindOfName where
  icod_ DefName        = icode0'
  icod_ ConName        = icode0 1
  icod_ FldName        = icode0 2
  icod_ PatternSynName = icode0 3
  icod_ QuotableName   = icode0 4
  icod_ MacroName      = icode0 5

  value = vcase valu where
    valu []  = valuN DefName
    valu [1] = valuN ConName
    valu [2] = valuN FldName
    valu [3] = valuN PatternSynName
    valu [4] = valuN QuotableName
    valu [5] = valuN MacroName
    valu _   = malformed

instance EmbPrj LocalVar where
  icod_ (LocalVar a b c)  = icode3' a b c

  value = value3 LocalVar

instance EmbPrj ConPatInfo where
  icod_ (ConPatInfo a _) = icod_ a
  value a                = flip ConPatInfo patNoRange <$> value a

-- Only for pattern synonyms (where a is Void)
instance EmbPrj a => EmbPrj (A.Pattern' a) where
  icod_ (A.VarP a)            = icode1 0 a
  icod_ (A.ConP a b c)        = icode3 1 a b c
  icod_ (A.DefP _ a b)        = icode2 2 a b
  icod_ (A.WildP _)           = icode0 3
  icod_ (A.AsP _ a b)         = icode2 4 a b
  icod_ (A.DotP _ a b)        = icode2 5 a b
  icod_ (A.AbsurdP _)         = icode0 6
  icod_ (A.LitP a)            = icode1 7 a
  icod_ (A.ProjP _ a b)       = icode2 8 a b
  icod_ (A.PatternSynP _ a b) = icode2 9 a b
  icod_ (A.RecP _ a)          = icode1 10 a

  value = vcase valu where
    valu [0, a]       = valuN A.VarP a
    valu [1, a, b, c] = valuN A.ConP a b c
    valu [2, a, b]    = valuN (A.DefP i) a b
    valu [3]          = valuN (A.WildP i)
    valu [4, a, b]    = valuN (A.AsP i) a b
    valu [5, a, b]    = valuN (A.DotP i) a b
    valu [6]          = valuN (A.AbsurdP i)
    valu [7, a]       = valuN (A.LitP) a
    valu [8, a, b]    = valuN (A.ProjP i) a b
    valu [9, a, b]    = valuN (A.PatternSynP i) a b
    valu [10, a]      = valuN (A.RecP i) a
    valu _            = malformed

    i = patNoRange

instance EmbPrj Precedence where
  icod_ TopCtx                 = icode0'
  icod_ FunctionSpaceDomainCtx = icode0 1
  icod_ (LeftOperandCtx a)     = icode1 2 a
  icod_ (RightOperandCtx a)    = icode1 3 a
  icod_ FunctionCtx            = icode0 4
  icod_ ArgumentCtx            = icode0 5
  icod_ InsideOperandCtx       = icode0 6
  icod_ WithFunCtx             = icode0 7
  icod_ WithArgCtx             = icode0 8
  icod_ DotPatternCtx          = icode0 9

  value = vcase valu where
    valu []     = valuN TopCtx
    valu [1]    = valuN FunctionSpaceDomainCtx
    valu [2, a] = valuN LeftOperandCtx a
    valu [3, a] = valuN RightOperandCtx a
    valu [4]    = valuN FunctionCtx
    valu [5]    = valuN ArgumentCtx
    valu [6]    = valuN InsideOperandCtx
    valu [7]    = valuN WithFunCtx
    valu [8]    = valuN WithArgCtx
    valu [9]    = valuN DotPatternCtx
    valu _      = malformed

instance EmbPrj ScopeInfo where
  icod_ (ScopeInfo a b c d _ _ _) = icode4' a b c d

  value = value4 (\ a b c d -> ScopeInfo a b c d Map.empty Map.empty Set.empty)
