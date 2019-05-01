
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Serialise.Instances.Abstract where

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

import Agda.Utils.Impossible

instance EmbPrj A.BindName where
  icod_ (A.BindName n) = icodeN' A.BindName n
  value = valueN A.BindName

instance EmbPrj Scope where
  icod_ (Scope a b c d e) = icodeN' Scope a b c d e

  value = valueN Scope

instance EmbPrj NameSpaceId where
  icod_ PublicNS        = icodeN' PublicNS
  icod_ PrivateNS       = icodeN 1 PrivateNS
  icod_ ImportedNS      = icodeN 2 ImportedNS
  icod_ OnlyQualifiedNS = icodeN 3 OnlyQualifiedNS

  value = vcase valu where
    valu []  = valuN PublicNS
    valu [1] = valuN PrivateNS
    valu [2] = valuN ImportedNS
    valu [3] = valuN OnlyQualifiedNS
    valu _   = malformed

instance EmbPrj Access where
  icod_ (PrivateAccess UserWritten) = icodeN 0 ()
  icod_ PrivateAccess{}             = icodeN 1 ()
  icod_ PublicAccess                = icodeN' PublicAccess
  icod_ OnlyQualified               = icodeN 2 ()

  value = vcase valu where
    valu [0] = valuN $ PrivateAccess UserWritten
    valu [1] = valuN $ PrivateAccess Inserted
    valu []  = valuN PublicAccess
    valu [2] = valuN OnlyQualified
    valu _   = malformed

instance EmbPrj NameSpace where
  icod_ (NameSpace a b c) = icodeN' NameSpace a b c

  value = valueN NameSpace

instance EmbPrj WhyInScope where
  icod_ Defined       = icodeN' Defined
  icod_ (Opened a b)  = icodeN 0 Opened a b
  icod_ (Applied a b) = icodeN 1 Applied a b

  value = vcase valu where
    valu []        = valuN Defined
    valu [0, a, b] = valuN Opened a b
    valu [1, a, b] = valuN Applied a b
    valu _         = malformed

instance EmbPrj AbstractName where
  icod_ (AbsName a b c d) = icodeN' AbsName a b c d

  value = valueN AbsName

instance EmbPrj NameMetadata where
  icod_ NoMetadata                  = icodeN' NoMetadata
  icod_ (GeneralizedVarsMetadata a) = icodeN' GeneralizedVarsMetadata a

  value = vcase valu where
    valu []  = valuN NoMetadata
    valu [a] = valuN GeneralizedVarsMetadata a
    valu _   = malformed

instance EmbPrj AbstractModule where
  icod_ (AbsModule a b) = icodeN' AbsModule a b

  value = valueN AbsModule

instance EmbPrj KindOfName where
  icod_ DefName        = icodeN' DefName
  icod_ ConName        = icodeN 1 ConName
  icod_ FldName        = icodeN 2 FldName
  icod_ PatternSynName = icodeN 3 PatternSynName
  icod_ QuotableName   = icodeN 4 QuotableName
  icod_ MacroName      = icodeN 5 MacroName
  icod_ GeneralizeName = icodeN 6 GeneralizeName
  icod_ DisallowedGeneralizeName = icodeN 7 DisallowedGeneralizeName

  value = vcase valu where
    valu []  = valuN DefName
    valu [1] = valuN ConName
    valu [2] = valuN FldName
    valu [3] = valuN PatternSynName
    valu [4] = valuN QuotableName
    valu [5] = valuN MacroName
    valu [6] = valuN GeneralizeName
    valu [7] = valuN DisallowedGeneralizeName
    valu _   = malformed

instance EmbPrj Binder where
  icod_ LambdaBound   = icodeN' LambdaBound
  icod_ PatternBound  = icodeN 1 PatternBound
  icod_ LetBound      = icodeN 2 LetBound

  value = vcase valu where
    valu []  = valuN LambdaBound
    valu [1] = valuN PatternBound
    valu [2] = valuN LetBound
    valu _   = malformed

instance EmbPrj LocalVar where
  icod_ (LocalVar a b c)  = icodeN' LocalVar a b c

  value = valueN LocalVar

instance EmbPrj ConPatInfo where
  icod_ (ConPatInfo a _ b) = icodeN' (\a b -> ConPatInfo a patNoRange b) a b

  value = valueN $ \a b -> ConPatInfo a patNoRange b

instance EmbPrj ConPatLazy

-- Only for pattern synonyms (where a is Void)
instance EmbPrj a => EmbPrj (A.Pattern' a) where
  icod_ (A.VarP a)            = icodeN 0 A.VarP a
  icod_ (A.ConP a b c)        = icodeN 1 A.ConP a b c
  icod_ (A.DefP p a b)        = icodeN 2 (A.DefP p) a b
  icod_ t@(A.WildP p)         = icodeN 3 t
  icod_ (A.AsP p a b)         = icodeN 4 (A.AsP p) a b
  icod_ (A.DotP p a)          = icodeN 5 (A.DotP p) a
  icod_ t@(A.AbsurdP _)       = icodeN 6 t
  icod_ (A.LitP a)            = icodeN 7 A.LitP a
  icod_ (A.ProjP p a b)       = icodeN 8 (A.ProjP p) a b
  icod_ (A.PatternSynP p a b) = icodeN 9 (A.PatternSynP p) a b
  icod_ (A.RecP p a)          = icodeN 10 (A.RecP p) a
  icod_ (A.EqualP _ a)        = __IMPOSSIBLE__
  icod_ (A.WithP i a)         = icodeN 11 (A.WithP i) a

  value = vcase valu where
    valu [0, a]       = valuN A.VarP a
    valu [1, a, b, c] = valuN A.ConP a b c
    valu [2, a, b]    = valuN (A.DefP i) a b
    valu [3]          = valuN (A.WildP i)
    valu [4, a, b]    = valuN (A.AsP i) a b
    valu [5, a]       = valuN (A.DotP i) a
    valu [6]          = valuN (A.AbsurdP i)
    valu [7, a]       = valuN (A.LitP) a
    valu [8, a, b]    = valuN (A.ProjP i) a b
    valu [9, a, b]    = valuN (A.PatternSynP i) a b
    valu [10, a]      = valuN (A.RecP i) a
    valu [11, a]      = valuN (A.WithP i) a
    valu _            = malformed

    i = patNoRange

instance EmbPrj ParenPreference where
  icod_ PreferParen     = icodeN' PreferParen
  icod_ PreferParenless = icodeN 1 PreferParenless
  value = vcase valu where
    valu []  = valuN PreferParen
    valu [1] = valuN PreferParenless
    valu _   = malformed

instance EmbPrj Precedence where
  icod_ TopCtx                 = icodeN' TopCtx
  icod_ FunctionSpaceDomainCtx = icodeN 1 FunctionSpaceDomainCtx
  icod_ (LeftOperandCtx a)     = icodeN 2 LeftOperandCtx a
  icod_ (RightOperandCtx a b)  = icodeN 3 RightOperandCtx a b
  icod_ FunctionCtx            = icodeN 4 FunctionCtx
  icod_ (ArgumentCtx a)        = icodeN 5 ArgumentCtx a
  icod_ InsideOperandCtx       = icodeN 6 InsideOperandCtx
  icod_ WithFunCtx             = icodeN 7 WithFunCtx
  icod_ WithArgCtx             = icodeN 8 WithArgCtx
  icod_ DotPatternCtx          = icodeN 9 DotPatternCtx

  value = vcase valu where
    valu []        = valuN TopCtx
    valu [1]       = valuN FunctionSpaceDomainCtx
    valu [2, a]    = valuN LeftOperandCtx a
    valu [3, a, b] = valuN RightOperandCtx a b
    valu [4]       = valuN FunctionCtx
    valu [5, a]    = valuN ArgumentCtx a
    valu [6]       = valuN InsideOperandCtx
    valu [7]       = valuN WithFunCtx
    valu [8]       = valuN WithArgCtx
    valu [9]       = valuN DotPatternCtx
    valu _         = malformed

instance EmbPrj ScopeInfo where
  icod_ (ScopeInfo a b c d e f g h i j) = icodeN' (\ a b c d e -> ScopeInfo a b c d e f g h i j) a b c d e

  value = valueN (\ a b c d e -> ScopeInfo a b c d e Map.empty Map.empty Set.empty Map.empty Map.empty)
