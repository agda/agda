
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Serialise.Instances.Abstract where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Agda.Syntax.Common
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Info
import Agda.Syntax.Scope.Base
import Agda.Syntax.Fixity

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common () --instance only

import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.Impossible

-- Don't serialize the tactic.
instance EmbPrj A.BindName where
  icod_ (A.BindName a) = icodeN' A.BindName a
  value = valueN A.BindName

instance EmbPrj Scope where
  icod_ (Scope a b c d e) = icodeN' Scope a b c d e

  value = valueN Scope

instance EmbPrj DataOrRecordModule where
  icod_ IsDataModule   = pure 0
  icod_ IsRecordModule = pure 1

  value = \case
    0 -> pure IsDataModule
    1 -> pure IsRecordModule
    _ -> malformed

instance EmbPrj NameSpaceId where
  icod_ PublicNS        = pure 0
  icod_ PrivateNS       = pure 1
  icod_ ImportedNS      = pure 2

  value = \case
    0 -> pure PublicNS
    1 -> pure PrivateNS
    2 -> pure ImportedNS
    _ -> malformed

instance EmbPrj Access where
  icod_ (PrivateAccess UserWritten) = pure 0
  icod_ PrivateAccess{}             = pure 1
  icod_ PublicAccess                = pure 2

  value = \case
    0 -> pure $ PrivateAccess UserWritten
    1 -> pure $ PrivateAccess Inserted
    2 -> pure PublicAccess
    _ -> malformed

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

-- Issue #1346: QNames are shared on their nameIds, so serializing will lose fixity information for
-- rebound fixities. We don't care about that in terms, but in the scope it's important to keep the
-- right fixity. Thus serialize the fixity separately.

data AbsNameWithFixity = AbsNameWithFixity Fixity A.QName KindOfName WhyInScope NameMetadata

toAbsName :: AbsNameWithFixity -> AbstractName
toAbsName (AbsNameWithFixity fx a b c d) = AbsName (set lensFixity fx a) b c d

fromAbsName :: AbstractName -> AbsNameWithFixity
fromAbsName (AbsName a b c d) = AbsNameWithFixity (a ^. lensFixity) a b c d

instance EmbPrj AbsNameWithFixity where
  icod_ (AbsNameWithFixity a b c d e) = icodeN' AbsNameWithFixity a b c d e
  value = valueN AbsNameWithFixity

instance EmbPrj AbstractName where
  icod_ a = icod_ (fromAbsName a)
  value = toAbsName <.> value

instance EmbPrj NameMetadata where
  icod_ NoMetadata                  = icodeN' NoMetadata
  icod_ (GeneralizedVarsMetadata a) = icodeN' GeneralizedVarsMetadata a

  value = vcase valu where
    valu []  = valuN NoMetadata
    valu [a] = valuN GeneralizedVarsMetadata a
    valu _   = malformed

instance EmbPrj A.Suffix where
  icod_ A.NoSuffix   = icodeN' A.NoSuffix
  icod_ (A.Suffix a) = icodeN' A.Suffix a

  value = vcase valu where
    valu []  = valuN A.NoSuffix
    valu [a] = valuN A.Suffix a
    valu _   = malformed

instance EmbPrj AbstractModule where
  icod_ (AbsModule a b) = icodeN' AbsModule a b

  value = valueN AbsModule

instance EmbPrj KindOfName where
  -- -- Enums have a generic EmbPrj
  --
  -- icod_ DefName        = icodeN' DefName
  -- icod_ ConName        = icodeN 1 ConName
  -- icod_ FldName        = icodeN 2 FldName
  -- icod_ PatternSynName = icodeN 3 PatternSynName
  -- icod_ QuotableName   = icodeN 4 QuotableName
  -- icod_ MacroName      = icodeN 5 MacroName
  -- icod_ GeneralizeName = icodeN 6 GeneralizeName
  -- icod_ DisallowedGeneralizeName = icodeN 7 DisallowedGeneralizeName

  -- value = vcase valu where
  --   valu []  = valuN DefName
  --   valu [1] = valuN ConName
  --   valu [2] = valuN FldName
  --   valu [3] = valuN PatternSynName
  --   valu [4] = valuN QuotableName
  --   valu [5] = valuN MacroName
  --   valu [6] = valuN GeneralizeName
  --   valu [7] = valuN DisallowedGeneralizeName
  --   valu _   = malformed

instance EmbPrj BindingSource where
  icod_ LambdaBound   = pure 0
  icod_ PatternBound  = pure 1
  icod_ LetBound      = pure 2
  icod_ WithBound     = pure 3

  value = \case
    0 -> pure LambdaBound
    1 -> pure PatternBound
    2 -> pure LetBound
    3 -> pure WithBound
    _ -> malformed

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
  icod_ (A.LitP i a)          = icodeN 7 (A.LitP i) a
  icod_ (A.ProjP p a b)       = icodeN 8 (A.ProjP p) a b
  icod_ (A.PatternSynP p a b) = icodeN 9 (A.PatternSynP p) a b
  icod_ (A.RecP p a)          = icodeN 10 (A.RecP p) a
  icod_ (A.EqualP _ a)        = __IMPOSSIBLE__
  icod_ (A.WithP i a)         = icodeN 11 (A.WithP i) a
  icod_ (A.AnnP i a p)        = icodeN 12 (A.AnnP i) a p

  value = vcase valu where
    valu [0, a]       = valuN A.VarP a
    valu [1, a, b, c] = valuN A.ConP a b c
    valu [2, a, b]    = valuN (A.DefP i) a b
    valu [3]          = valuN (A.WildP i)
    valu [4, a, b]    = valuN (A.AsP i) a b
    valu [5, a]       = valuN (A.DotP i) a
    valu [6]          = valuN (A.AbsurdP i)
    valu [7, a]       = valuN (A.LitP i) a
    valu [8, a, b]    = valuN (A.ProjP i) a b
    valu [9, a, b]    = valuN (A.PatternSynP i) a b
    valu [10, a]      = valuN (A.RecP i) a
    valu [11, a]      = valuN (A.WithP i) a
    valu [12, a, b]   = valuN (A.AnnP i) a b
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

instance EmbPrj NameOrModule
