{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Agda.TypeChecking.Serialise.Instances.Abstract where

import Control.Monad
import Control.Monad.Reader

import Data.HashMap.Strict qualified as HMap
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Void (Void)

import Agda.Syntax.Abstract.Name
  ( AbstractName(..), AbstractModule(..), KindOfName, NameMetadata(..), WhyInScope(..) )
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Pattern ( noDotOrEqPattern )
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Info
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common (SerialisedRange(..))

import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.Null

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
  icod_ (PrivateAccess _ UserWritten) = pure 0
  icod_ PrivateAccess{}               = pure 1
  icod_ PublicAccess                  = pure 2

  value = \case
    0 -> pure $ PrivateAccess empty UserWritten
    1 -> pure $ privateAccessInserted
    2 -> pure PublicAccess
    _ -> malformed

instance EmbPrj NameSpace where
  icod_ (NameSpace a b c d) = icodeN' NameSpace a b c d

  value = valueN NameSpace

-- Andreas, 2025-10-23:
-- We serialize the Ranges in WhyInScope
-- so that we have then e.g. in the ClashingDefinition error.

instance EmbPrj WhyInScope where
  icod_ Defined       = icodeN' Defined
  icod_ (Opened a b)  = icodeN 0 (\(_ :: SerialisedRange) -> Opened) (SerialisedRange (getRange a)) a b
  icod_ (Applied a b) = icodeN 1 (\(_ :: SerialisedRange) -> Applied) (SerialisedRange (getRange a)) a b

  value = vcase \case
    N0           -> valuN Defined
    (N4 0 r a b) -> valuN (\(SerialisedRange r) a b -> Opened (setRange r a) b) r a b
    (N4 1 r a b) -> valuN (\(SerialisedRange r) a b -> Applied (setRange r a) b) r a b
    _            -> malformed

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
  icod_ (NameMetadata a b) = icodeN' NameMetadata a b
  value = valueN NameMetadata

instance EmbPrj A.Suffix where
  icod_ A.NoSuffix   = icodeN' A.NoSuffix
  icod_ (A.Suffix a) = icodeN' A.Suffix a

  value = vcase valu where
    valu N0     = valuN A.NoSuffix
    valu (N1 a) = valuN A.Suffix a
    valu _      = malformed

instance EmbPrj AbstractModule where
  icod_ (AbsModule a b) = icodeN' AbsModule a b

  value = valueN AbsModule

instance EmbPrj KindOfName where
  -- Enums have a generic EmbPrj

instance EmbPrj BindingSource where
  icod_ = \case
    LambdaBound     -> pure 0
    PatternBound _  -> pure 1
    LetBound        -> pure 2
    WithBound       -> pure 3
    MacroBound      -> pure 4

  value = \case
    0 -> pure LambdaBound
    1 -> pure $ PatternBound empty
    2 -> pure LetBound
    3 -> pure WithBound
    4 -> pure MacroBound
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
  icod_ x = ReaderT \dict -> case x of
    (A.VarP a)            -> runReaderT (icodeN 0 A.VarP a) dict
    (A.ConP a b c)        -> runReaderT (icodeN 1 A.ConP a b c) dict
    (A.DefP p a b)        -> runReaderT (icodeN 2 (A.DefP p) a b) dict
    t@(A.WildP p)         -> runReaderT (icodeN 3 t) dict
    (A.AsP p a b)         -> runReaderT (icodeN 4 (A.AsP p) a b) dict
    (A.DotP r a)          -> runReaderT (icodeN 5 (A.DotP r) a) dict
    t@(A.AbsurdP _)       -> runReaderT (icodeN 6 t) dict
    (A.LitP i a)          -> runReaderT (icodeN 7 (A.LitP i) a) dict
    (A.ProjP p a b)       -> runReaderT (icodeN 8 (A.ProjP p) a b) dict
    (A.PatternSynP p a b) -> runReaderT (icodeN 9 (A.PatternSynP p) a b) dict
    (A.RecP r a b)        -> runReaderT (icodeN 10 (A.RecP r) a b) dict
    (A.EqualP _ a)        -> __IMPOSSIBLE__ dict
    (A.WithP i a)         -> runReaderT (icodeN 11 (A.WithP i) a) dict

  value x = ReaderT \dict -> runReaderT (vcase valu x) dict where
    valu x = ReaderT \dict -> case x of
      (N2 0 a)     -> runReaderT (valuN A.VarP a) dict
      (N4 1 a b c) -> runReaderT (valuN A.ConP a b c) dict
      (N3 2 a b)   -> runReaderT (valuN (A.DefP i) a b) dict
      (N1 3)       -> runReaderT (valuN (A.WildP i)) dict
      (N3 4 a b)   -> runReaderT (valuN (A.AsP i) a b) dict
      (N2 5 a)     -> runReaderT (valuN (A.DotP i) a) dict
      (N1 6)       -> runReaderT (valuN (A.AbsurdP i)) dict
      (N2 7 a)     -> runReaderT (valuN (A.LitP i) a) dict
      (N3 8 a b)   -> runReaderT (valuN (A.ProjP i) a b) dict
      (N3 9 a b)   -> runReaderT (valuN (A.PatternSynP i) a b) dict
      (N3 10 a b)  -> runReaderT (valuN (A.RecP empty) a b) dict
      (N2 11 a)    -> runReaderT (valuN (A.WithP i) a) dict
      _            -> malformedIO

    i = patNoRange

-- | Hackish serialization for patterns that deletes dot patterns.
--   So that we can serialize the 'WithClauseProjectionFixityMismatch'
--   without having to define serialization of expressions.
--
instance {-# OVERLAPS #-} EmbPrj A.Pattern where
  icod_ = icod_ <=< noDotOrEqPattern (return $ A.WildP empty)
  value = fmap (__IMPOSSIBLE__ :: Void -> A.Expr) <.> value

instance EmbPrj A.PatternSynDefn where
  icod_ (A.PatternSynDefn a b) = icodeN' A.PatternSynDefn a b
  value = vcase \case
    N2 a b -> valuN A.PatternSynDefn a b
    _ -> malformed

instance EmbPrj ParenPreference where
  icod_ PreferParen     = icodeN' PreferParen
  icod_ PreferParenless = icodeN 1 PreferParenless
  value = vcase valu where
    valu N0     = valuN PreferParen
    valu (N1 1) = valuN PreferParenless
    valu _      = malformed

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
    valu N0         = valuN TopCtx
    valu (N1 1)     = valuN FunctionSpaceDomainCtx
    valu (N2 2 a)   = valuN LeftOperandCtx a
    valu (N3 3 a b) = valuN RightOperandCtx a b
    valu (N1 4)     = valuN FunctionCtx
    valu (N2 5 a)   = valuN ArgumentCtx a
    valu (N1 6)     = valuN InsideOperandCtx
    valu (N1 7)     = valuN WithFunCtx
    valu (N1 8)     = valuN WithArgCtx
    valu (N1 9)     = valuN DotPatternCtx
    valu _          = malformed

instance EmbPrj ScopeInfo where
  icod_ (ScopeInfo a b c d e f g h i j k) = icodeN' (\ a b c d e -> ScopeInfo a b c d e f g h i j k) a b c d e

  value = valueN (\ a b c d e -> ScopeInfo a b c d e HMap.empty HMap.empty Set.empty Map.empty Map.empty Map.empty)

instance EmbPrj NameOrModule
