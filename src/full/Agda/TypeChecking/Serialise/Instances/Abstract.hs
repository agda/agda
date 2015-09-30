{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Agda.TypeChecking.Serialise.Instances.Abstract where

import Control.Applicative

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
  value = vcase valu where valu [a, b, c, d, e] = valu5 Scope a b c d e
                           valu _               = malformed

instance EmbPrj NameSpaceId where
  icod_ PublicNS        = icode0'
  icod_ PrivateNS       = icode0 1
  icod_ ImportedNS      = icode0 2
  icod_ OnlyQualifiedNS = icode0 3
  value = vcase valu where valu []  = valu0 PublicNS
                           valu [1] = valu0 PrivateNS
                           valu [2] = valu0 ImportedNS
                           valu [3] = valu0 OnlyQualifiedNS
                           valu _   = malformed

instance EmbPrj Access where
  icod_ PrivateAccess = icode0 0
  icod_ PublicAccess  = icode0'
  icod_ OnlyQualified = icode0 2
  value = vcase valu where valu [0] = valu0 PrivateAccess
                           valu []  = valu0 PublicAccess
                           valu [2] = valu0 OnlyQualified
                           valu _   = malformed

instance EmbPrj NameSpace where
  icod_ (NameSpace a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 NameSpace a b
                           valu _      = malformed

instance EmbPrj WhyInScope where
  icod_ Defined       = icode0'
  icod_ (Opened a b)  = icode2 0 a b
  icod_ (Applied a b) = icode2 1 a b
  value = vcase valu where valu []        = valu0 Defined
                           valu [0, a, b] = valu2 Opened a b
                           valu [1, a, b] = valu2 Applied a b
                           valu _         = malformed

instance EmbPrj AbstractName where
  icod_ (AbsName a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 AbsName a b c
                           valu _         = malformed

instance EmbPrj AbstractModule where
  icod_ (AbsModule a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 AbsModule a b
                           valu _      = malformed

instance EmbPrj KindOfName where
  icod_ DefName        = icode0'
  icod_ ConName        = icode0 1
  icod_ FldName        = icode0 2
  icod_ PatternSynName = icode0 3
  icod_ QuotableName   = icode0 4
  icod_ MacroName      = icode0 5
  value = vcase valu where valu []  = valu0 DefName
                           valu [1] = valu0 ConName
                           valu [2] = valu0 FldName
                           valu [3] = valu0 PatternSynName
                           valu [4] = valu0 QuotableName
                           valu [5] = valu0 MacroName
                           valu _   = malformed

instance EmbPrj LocalVar where
  icod_ (LocalVar a)      = icode1' a
  icod_ (ShadowedVar a b) = icode2' a b
  value = vcase valu where valu [a]    = valu1 LocalVar a
                           valu [a, b] = valu2 ShadowedVar a b
                           valu _      = malformed

instance EmbPrj ConPatInfo where
  icod_ (ConPatInfo a _) = icod_ a
  value a = flip ConPatInfo patNoRange <$> value a

-- Only for pattern synonyms (where a is Void)
instance EmbPrj a => EmbPrj (A.Pattern' a) where
  icod_ (A.VarP a)            = icode1 0 a
  icod_ (A.ConP a b c)        = icode3 1 a b c
  icod_ (A.DefP _ a b)        = icode2 2 a b
  icod_ (A.WildP _)           = icode0 3
  icod_ (A.AsP _ a b)         = icode2 4 a b
  icod_ (A.DotP _ a)          = icode1 5 a
  icod_ (A.AbsurdP _)         = icode0 6
  icod_ (A.LitP a)            = icode1 7 a
  icod_ (A.PatternSynP _ a b) = icode2 9 a b
  icod_ (A.RecP _ a)          = icode1 10 a

  value = vcase valu
    where
     valu [0, a]       = valu1 A.VarP a
     valu [1, a, b, c] = valu3 A.ConP a b c
     valu [2, a, b]    = valu2 (A.DefP i) a b
     valu [3]          = valu0 (A.WildP i)
     valu [4, a, b]    = valu2 (A.AsP i) a b
     valu [5, a]       = valu1 (A.DotP i) a
     valu [6]          = valu0 (A.AbsurdP i)
     valu [7, a]       = valu1 (A.LitP) a
     valu [9, a, b]    = valu2 (A.PatternSynP i) a b
     valu [10, a]      = valu1 (A.RecP i) a
     valu _            = malformed

     i  = patNoRange

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
  value = vcase valu
    where
    valu []     = valu0 TopCtx
    valu [1]    = valu0 FunctionSpaceDomainCtx
    valu [2, a] = valu1 LeftOperandCtx a
    valu [3, a] = valu1 RightOperandCtx a
    valu [4]    = valu0 FunctionCtx
    valu [5]    = valu0 ArgumentCtx
    valu [6]    = valu0 InsideOperandCtx
    valu [7]    = valu0 WithFunCtx
    valu [8]    = valu0 WithArgCtx
    valu [9]    = valu0 DotPatternCtx
    valu _      = malformed

instance EmbPrj ScopeInfo where
  icod_ (ScopeInfo a b c d) = icode4' a b c d
  value = vcase valu where valu [a, b, c, d] = valu4 ScopeInfo a b c d
                           valu _            = malformed

