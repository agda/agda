{-# OPTIONS_GHC -fno-warn-orphans     #-}

module Agda.TypeChecking.Serialise.Instances.Errors where

import Control.Monad

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Internal () --instance only
import Agda.TypeChecking.Serialise.Instances.Abstract () --instance only

import Agda.Syntax.Concrete.Definitions (DeclarationWarning(..), DeclarationWarning'(..))
import Agda.Syntax.Parser.Monad
import Agda.TypeChecking.Monad.Base
import Agda.Interaction.Options
import Agda.Interaction.Options.Warnings
import Agda.Interaction.Library.Base
import Agda.Termination.CutOff
import Agda.Utils.Pretty
import Agda.Utils.ProfileOptions

import Agda.Utils.Impossible

instance EmbPrj TCWarning where
  icod_ (TCWarning fp a b c d) = icodeN' TCWarning fp a b c d
  value = valueN TCWarning

-- We don't need to serialise warnings that turn into errors
instance EmbPrj Warning where
  icod_ = \case
    TerminationIssue a                    -> __IMPOSSIBLE__
    UnreachableClauses a b                -> icodeN 0 UnreachableClauses a b
    CoverageIssue a b                     -> __IMPOSSIBLE__
    NotStrictlyPositive a b               -> __IMPOSSIBLE__
    UnsolvedMetaVariables a               -> __IMPOSSIBLE__
    UnsolvedInteractionMetas a            -> __IMPOSSIBLE__
    UnsolvedConstraints a                 -> __IMPOSSIBLE__
    OldBuiltin a b                        -> icodeN 1 OldBuiltin a b
    EmptyRewritePragma                    -> icodeN 2 EmptyRewritePragma
    UselessPublic                         -> icodeN 3 UselessPublic
    UselessInline a                       -> icodeN 4 UselessInline a
    GenericWarning a                      -> icodeN 5 GenericWarning a
    GenericNonFatalError a                -> __IMPOSSIBLE__
    SafeFlagPostulate a                   -> __IMPOSSIBLE__
    SafeFlagPragma a                      -> __IMPOSSIBLE__
    SafeFlagNonTerminating                -> __IMPOSSIBLE__
    SafeFlagTerminating                   -> __IMPOSSIBLE__
    SafeFlagWithoutKFlagPrimEraseEquality -> __IMPOSSIBLE__
    SafeFlagNoPositivityCheck             -> __IMPOSSIBLE__
    SafeFlagPolarity                      -> __IMPOSSIBLE__
    SafeFlagNoUniverseCheck               -> __IMPOSSIBLE__
    SafeFlagNoCoverageCheck               -> __IMPOSSIBLE__
    SafeFlagInjective                     -> __IMPOSSIBLE__
    SafeFlagEta                           -> __IMPOSSIBLE__
    DeprecationWarning a b c              -> icodeN 6 DeprecationWarning a b c
    NicifierIssue a                       -> icodeN 7 NicifierIssue a
    InversionDepthReached a               -> icodeN 8 InversionDepthReached a
    UserWarning a                         -> icodeN 9 UserWarning a
    AbsurdPatternRequiresNoRHS a          -> icodeN 10 AbsurdPatternRequiresNoRHS a
    ModuleDoesntExport a b c d            -> icodeN 11 ModuleDoesntExport a b c d
    LibraryWarning a                      -> icodeN 12 LibraryWarning a
    CoverageNoExactSplit a b              -> icodeN 13 CoverageNoExactSplit a b
    CantGeneralizeOverSorts a             -> icodeN 14 CantGeneralizeOverSorts a
    IllformedAsClause a                   -> icodeN 15 IllformedAsClause a
    WithoutKFlagPrimEraseEquality         -> icodeN 16 WithoutKFlagPrimEraseEquality
    InstanceWithExplicitArg a             -> icodeN 17 InstanceWithExplicitArg a
    InfectiveImport a b                   -> icodeN 18 InfectiveImport a b
    CoInfectiveImport a b                 -> icodeN 19 CoInfectiveImport a b
    InstanceNoOutputTypeName a            -> icodeN 20 InstanceNoOutputTypeName a
    InstanceArgWithExplicitArg a          -> icodeN 21 InstanceArgWithExplicitArg a
    WrongInstanceDeclaration              -> icodeN 22 WrongInstanceDeclaration
    RewriteNonConfluent a b c d           -> icodeN 23 RewriteNonConfluent a b c d
    RewriteMaybeNonConfluent a b c        -> icodeN 24 RewriteMaybeNonConfluent a b c
    PragmaCompileErased a b               -> icodeN 25 PragmaCompileErased a b
    FixityInRenamingModule a              -> icodeN 26 FixityInRenamingModule a
    NotInScopeW ns                        -> icodeN 27 NotInScopeW ns
    ClashesViaRenaming a b                -> icodeN 28 ClashesViaRenaming a b
    RecordFieldWarning a                  -> icodeN 29 RecordFieldWarning a
    UselessPatternDeclarationForRecord a  -> icodeN 30 UselessPatternDeclarationForRecord a
    EmptyWhere                            -> icodeN 31 EmptyWhere
    AsPatternShadowsConstructorOrPatternSynonym a -> icodeN 32 AsPatternShadowsConstructorOrPatternSynonym a
    DuplicateUsing a                      -> icodeN 33 DuplicateUsing a
    UselessHiding a                       -> icodeN 34 UselessHiding a
    GenericUseless a b                    -> icodeN 35 GenericUseless a b
    RewriteAmbiguousRules a b c           -> icodeN 36 RewriteAmbiguousRules a b c
    RewriteMissingRule a b c              -> icodeN 37 RewriteMissingRule a b c
    ParseWarning a                        -> icodeN 38 ParseWarning a
    NoGuardednessFlag a                   -> icodeN 39 NoGuardednessFlag a
    NoEquivWhenSplitting a                -> icodeN 40 NoEquivWhenSplitting a

  value = vcase $ \ case
    [0, a, b]            -> valuN UnreachableClauses a b
    [1, a, b]            -> valuN OldBuiltin a b
    [2]                  -> valuN EmptyRewritePragma
    [3]                  -> valuN UselessPublic
    [4, a]               -> valuN UselessInline a
    [5, a]               -> valuN GenericWarning a
    [6, a, b, c]         -> valuN DeprecationWarning a b c
    [7, a]               -> valuN NicifierIssue a
    [8, a]               -> valuN InversionDepthReached a
    [9, a]               -> valuN UserWarning a
    [10, a]              -> valuN AbsurdPatternRequiresNoRHS a
    [11, a, b, c, d]     -> valuN ModuleDoesntExport a b c d
    [12, a]              -> valuN LibraryWarning a
    [13, a, b]           -> valuN CoverageNoExactSplit a b
    [14, a]              -> valuN CantGeneralizeOverSorts a
    [15, a]              -> valuN IllformedAsClause a
    [16]                 -> valuN WithoutKFlagPrimEraseEquality
    [17, a]              -> valuN InstanceWithExplicitArg a
    [18, a, b]           -> valuN InfectiveImport a b
    [19, a, b]           -> valuN CoInfectiveImport a b
    [20, a]              -> valuN InstanceNoOutputTypeName a
    [21, a]              -> valuN InstanceArgWithExplicitArg a
    [22]                 -> valuN WrongInstanceDeclaration
    [23, a, b, c, d]     -> valuN RewriteNonConfluent a b c d
    [24, a, b, c]        -> valuN RewriteMaybeNonConfluent a b c
    [25, a, b]           -> valuN PragmaCompileErased a b
    [26, a]              -> valuN FixityInRenamingModule a
    [27, ns]             -> valuN NotInScopeW ns
    [28, a, b]           -> valuN ClashesViaRenaming a b
    [29, a]              -> valuN RecordFieldWarning a
    [30, a]              -> valuN UselessPatternDeclarationForRecord a
    [31]                 -> valuN EmptyWhere
    [32, a]              -> valuN AsPatternShadowsConstructorOrPatternSynonym a
    [33, a]              -> valuN DuplicateUsing a
    [34, a]              -> valuN UselessHiding a
    [35, a, b]           -> valuN GenericUseless a b
    [36, a, b, c]        -> valuN RewriteAmbiguousRules a b c
    [37, a, b, c]        -> valuN RewriteMissingRule a b c
    [38, a]              -> valuN ParseWarning a
    [39, a]              -> valuN NoGuardednessFlag a
    [40, a]              -> valuN NoEquivWhenSplitting a
    _ -> malformed

instance EmbPrj ParseWarning where
  icod_ = \case
    OverlappingTokensWarning a -> icodeN 0 OverlappingTokensWarning a
    UnsupportedAttribute a b   -> icodeN 1 UnsupportedAttribute a b
    MultipleAttributes a b     -> icodeN 2 MultipleAttributes a b

  value = vcase $ \case
    [0, a]    -> valuN OverlappingTokensWarning a
    [1, a, b] -> valuN UnsupportedAttribute a b
    [2, a, b] -> valuN MultipleAttributes a b
    _ -> malformed

instance EmbPrj RecordFieldWarning where
  icod_ = \case
    DuplicateFieldsWarning a   -> icodeN 0 DuplicateFieldsWarning a
    TooManyFieldsWarning a b c -> icodeN 1 TooManyFieldsWarning a b c

  value = vcase $ \case
    [0, a]       -> valuN DuplicateFieldsWarning a
    [1, a, b, c] -> valuN TooManyFieldsWarning a b c
    _ -> malformed

instance EmbPrj DeclarationWarning where
  icod_ (DeclarationWarning a b) = icodeN' DeclarationWarning a b
  value = vcase $ \case
    [a, b] -> valuN DeclarationWarning a b
    _ -> malformed

instance EmbPrj DeclarationWarning' where
  icod_ = \case
    UnknownNamesInFixityDecl a        -> icodeN 0 UnknownNamesInFixityDecl a
    UnknownNamesInPolarityPragmas a   -> icodeN 1 UnknownNamesInPolarityPragmas a
    PolarityPragmasButNotPostulates a -> icodeN 2 PolarityPragmasButNotPostulates a
    UselessPrivate a                  -> icodeN 3 UselessPrivate a
    UselessAbstract a                 -> icodeN 4 UselessAbstract a
    UselessInstance a                 -> icodeN 5 UselessInstance a
    EmptyMutual a                     -> icodeN 6 EmptyMutual a
    EmptyAbstract a                   -> icodeN 7 EmptyAbstract a
    EmptyPrivate a                    -> icodeN 8 EmptyPrivate a
    EmptyInstance a                   -> icodeN 9 EmptyInstance a
    EmptyMacro a                      -> icodeN 10 EmptyMacro a
    EmptyPostulate a                  -> icodeN 11 EmptyPostulate a
    InvalidTerminationCheckPragma a   -> icodeN 12 InvalidTerminationCheckPragma a
    InvalidNoPositivityCheckPragma a  -> icodeN 13 InvalidNoPositivityCheckPragma a
    InvalidCatchallPragma a           -> icodeN 14 InvalidCatchallPragma a
    InvalidNoUniverseCheckPragma a    -> icodeN 15 InvalidNoUniverseCheckPragma a
    UnknownFixityInMixfixDecl a       -> icodeN 16 UnknownFixityInMixfixDecl a
    MissingDefinitions a              -> icodeN 17 MissingDefinitions a
    NotAllowedInMutual r a            -> icodeN 18 NotAllowedInMutual r a
    PragmaNoTerminationCheck r        -> icodeN 19 PragmaNoTerminationCheck r
    EmptyGeneralize a                 -> icodeN 20 EmptyGeneralize a
    PragmaCompiled r                  -> icodeN 21 PragmaCompiled r
    EmptyPrimitive a                  -> icodeN 22 EmptyPrimitive a
    EmptyField r                      -> icodeN 23 EmptyField r
    ShadowingInTelescope nrs          -> icodeN 24 ShadowingInTelescope nrs
    InvalidCoverageCheckPragma r      -> icodeN 25 InvalidCoverageCheckPragma r
    OpenPublicAbstract r              -> icodeN 26 OpenPublicAbstract r
    OpenPublicPrivate r               -> icodeN 27 OpenPublicPrivate r
    EmptyConstructor a                -> icodeN 28 EmptyConstructor a
    InvalidRecordDirective a          -> icodeN 29 InvalidRecordDirective a
    InvalidConstructor a              -> icodeN 30 InvalidConstructor a
    InvalidConstructorBlock a         -> icodeN 31 InvalidConstructorBlock a
    MissingDeclarations a             -> icodeN 32 MissingDeclarations a

  value = vcase $ \case
    [0, a]   -> valuN UnknownNamesInFixityDecl a
    [1, a]   -> valuN UnknownNamesInPolarityPragmas a
    [2, a]   -> valuN PolarityPragmasButNotPostulates a
    [3, a]   -> valuN UselessPrivate a
    [4, a]   -> valuN UselessAbstract a
    [5, a]   -> valuN UselessInstance a
    [6, a]   -> valuN EmptyMutual a
    [7, a]   -> valuN EmptyAbstract a
    [8, a]   -> valuN EmptyPrivate a
    [9, a]   -> valuN EmptyInstance a
    [10,a]   -> valuN EmptyMacro a
    [11,a]   -> valuN EmptyPostulate a
    [12,a]   -> valuN InvalidTerminationCheckPragma a
    [13,a]   -> valuN InvalidNoPositivityCheckPragma a
    [14,a]   -> valuN InvalidCatchallPragma a
    [15,a]   -> valuN InvalidNoUniverseCheckPragma a
    [16,a]   -> valuN UnknownFixityInMixfixDecl a
    [17,a]   -> valuN MissingDefinitions a
    [18,r,a] -> valuN NotAllowedInMutual r a
    [19,r]   -> valuN PragmaNoTerminationCheck r
    [20,a]   -> valuN EmptyGeneralize a
    [21,a]   -> valuN PragmaCompiled a
    [22,a]   -> valuN EmptyPrimitive a
    [23,r]   -> valuN EmptyField r
    [24,nrs] -> valuN ShadowingInTelescope nrs
    [25,r]   -> valuN InvalidCoverageCheckPragma r
    [26,r]   -> valuN OpenPublicAbstract r
    [27,r]   -> valuN OpenPublicPrivate r
    [28,r]   -> valuN EmptyConstructor r
    [29,r]   -> valuN InvalidRecordDirective r
    [30,r]   -> valuN InvalidConstructor r
    [31,r]   -> valuN InvalidConstructorBlock r
    [32,r]   -> valuN MissingDeclarations r
    _ -> malformed

instance EmbPrj LibWarning where
  icod_ = \case
    LibWarning a b -> icodeN 0 LibWarning a b

  value = vcase $ \case
    [0, a, b]   -> valuN LibWarning a b
    _ -> malformed

instance EmbPrj LibWarning' where
  icod_ = \case
    UnknownField     a   -> icodeN 0 UnknownField a

  value = vcase $ \case
    [0, a]    -> valuN UnknownField a
    _ -> malformed

instance EmbPrj ExecutablesFile where
  icod_ = \case
    ExecutablesFile a b -> icodeN 0 ExecutablesFile a b

  value = vcase $ \case
    [0, a, b] -> valuN ExecutablesFile a b
    _ -> malformed

instance EmbPrj LibPositionInfo where
  icod_ = \case
    LibPositionInfo a b c -> icodeN 0 LibPositionInfo a b c

  value = vcase $ \case
    [0, a, b, c] -> valuN LibPositionInfo a b c
    _ -> malformed

instance EmbPrj Doc where
  icod_ d = icodeN' (undefined :: String -> Doc) (render d)

  value = valueN text

instance EmbPrj PragmaOptions where
  icod_ = \case
    PragmaOptions a b c d e f g h i j k l m n o p q r s t u v w x y z aa bb cc dd ee ff gg hh ii jj kk ll mm nn oo pp qq rr ss tt uu vv ww xx yy zz aaa bbb ccc ddd eee ->
      icodeN' PragmaOptions a b c d e f g h i j k l m n o p q r s t u v w x y z aa bb cc dd ee ff gg hh ii jj kk ll mm nn oo pp qq rr ss tt uu vv ww xx yy zz aaa bbb ccc ddd eee

  value = vcase $ \case
    [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, bb, cc, dd, ee, ff, gg, hh, ii, jj, kk, ll, mm, nn, oo, pp, qq, rr, ss, tt, uu, vv, ww, xx, yy, zz, aaa, bbb, ccc, ddd, eee] ->
      valuN PragmaOptions a b c d e f g h i j k l m n o p q r s t u v w x y z aa bb cc dd ee ff gg hh ii jj kk ll mm nn oo pp qq rr ss tt uu vv ww xx yy zz aaa bbb ccc ddd eee
    _ -> malformed

instance EmbPrj ProfileOptions where
  icod_ opts = icode (profileOptionsToList opts)
  value = fmap profileOptionsFromList . value

instance EmbPrj ProfileOption where
  icod_ = icode . fromEnum
  value = value >=> \ n -> if lo <= n && n <= hi then pure (toEnum n) else malformed
    where
      lo = fromEnum (minBound :: ProfileOption)
      hi = fromEnum (maxBound :: ProfileOption)

instance EmbPrj UnicodeOrAscii

instance EmbPrj ConfluenceCheck where
  icod_ LocalConfluenceCheck  = icodeN' LocalConfluenceCheck
  icod_ GlobalConfluenceCheck = icodeN 0 GlobalConfluenceCheck

  value = vcase valu where
    valu []  = valuN LocalConfluenceCheck
    valu [0] = valuN GlobalConfluenceCheck
    valu _   = malformed

instance EmbPrj WarningMode where
  icod_ = \case
    WarningMode a b -> icodeN' WarningMode a b

  value = vcase $ \case
    [a, b]   -> valuN WarningMode a b
    _ -> malformed

instance EmbPrj WarningName where
  icod_ x = icod_ (warningName2String x)

  value = (maybe malformed return . string2WarningName) <=< value


instance EmbPrj CutOff where
  icod_ = \case
    DontCutOff -> icodeN' DontCutOff
    CutOff a -> icodeN 0 CutOff a

  value = vcase valu where
    valu [] = valuN DontCutOff
    valu [0,a] = valuN CutOff a
    valu _ = malformed
