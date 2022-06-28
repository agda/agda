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
    HiddenGeneralize r                -> icodeN 33 HiddenGeneralize r

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
    [33,r]   -> valuN HiddenGeneralize r
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
    PragmaOptions a b c d e f g h i j k l m n o p q r s t u v w x y z aa bb cc dd ee ff gg hh ii jj kk ll mm nn oo pp qq rr ss tt uu vv ww xx yy zz aaa bbb ccc ddd ->
      icodeN' PragmaOptions a b c d e f g h i j k l m n o p q r s t u v w x y z aa bb cc dd ee ff gg hh ii jj kk ll mm nn oo pp qq rr ss tt uu vv ww xx yy zz aaa bbb ccc ddd

  value = vcase $ \case
    [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, bb, cc, dd, ee, ff, gg, hh, ii, jj, kk, ll, mm, nn, oo, pp, qq, rr, ss, tt, uu, vv, ww, xx, yy, zz, aaa, bbb, ccc, ddd] ->
      valuN PragmaOptions a b c d e f g h i j k l m n o p q r s t u v w x y z aa bb cc dd ee ff gg hh ii jj kk ll mm nn oo pp qq rr ss tt uu vv ww xx yy zz aaa bbb ccc ddd
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
  icod_ = \case
    OverlappingTokensWarning_                    -> icodeN  0 OverlappingTokensWarning_
    UnsupportedAttribute_                        -> icodeN  1 UnsupportedAttribute_
    MultipleAttributes_                          -> icodeN  2 MultipleAttributes_
    LibUnknownField_                             -> icodeN  3 LibUnknownField_
    EmptyAbstract_                               -> icodeN  4 EmptyAbstract_
    EmptyConstructor_                            -> icodeN  5 EmptyConstructor_
    EmptyField_                                  -> icodeN  6 EmptyField_
    EmptyGeneralize_                             -> icodeN  7 EmptyGeneralize_
    EmptyInstance_                               -> icodeN  8 EmptyInstance_
    EmptyMacro_                                  -> icodeN  9 EmptyMacro_
    EmptyMutual_                                 -> icodeN 10 EmptyMutual_
    EmptyPostulate_                              -> icodeN 11 EmptyPostulate_
    EmptyPrimitive_                              -> icodeN 12 EmptyPrimitive_
    EmptyPrivate_                                -> icodeN 13 EmptyPrivate_
    EmptyRewritePragma_                          -> icodeN 14 EmptyRewritePragma_
    EmptyWhere_                                  -> icodeN 15 EmptyWhere_
    HiddenGeneralize_                            -> icodeN 16 HiddenGeneralize_
    InvalidCatchallPragma_                       -> icodeN 17 InvalidCatchallPragma_
    InvalidConstructor_                          -> icodeN 18 InvalidConstructor_
    InvalidConstructorBlock_                     -> icodeN 19 InvalidConstructorBlock_
    InvalidCoverageCheckPragma_                  -> icodeN 20 InvalidCoverageCheckPragma_
    InvalidNoPositivityCheckPragma_              -> icodeN 21 InvalidNoPositivityCheckPragma_
    InvalidNoUniverseCheckPragma_                -> icodeN 22 InvalidNoUniverseCheckPragma_
    InvalidRecordDirective_                      -> icodeN 23 InvalidRecordDirective_
    InvalidTerminationCheckPragma_               -> icodeN 24 InvalidTerminationCheckPragma_
    MissingDeclarations_                         -> icodeN 25 MissingDeclarations_
    MissingDefinitions_                          -> icodeN 26 MissingDefinitions_
    NotAllowedInMutual_                          -> icodeN 27 NotAllowedInMutual_
    OpenPublicAbstract_                          -> icodeN 28 OpenPublicAbstract_
    OpenPublicPrivate_                           -> icodeN 29 OpenPublicPrivate_
    PolarityPragmasButNotPostulates_             -> icodeN 30 PolarityPragmasButNotPostulates_
    PragmaCompiled_                              -> icodeN 31 PragmaCompiled_
    PragmaNoTerminationCheck_                    -> icodeN 32 PragmaNoTerminationCheck_
    ShadowingInTelescope_                        -> icodeN 33 ShadowingInTelescope_
    UnknownFixityInMixfixDecl_                   -> icodeN 34 UnknownFixityInMixfixDecl_
    UnknownNamesInFixityDecl_                    -> icodeN 35 UnknownNamesInFixityDecl_
    UnknownNamesInPolarityPragmas_               -> icodeN 36 UnknownNamesInPolarityPragmas_
    UselessAbstract_                             -> icodeN 37 UselessAbstract_
    UselessInstance_                             -> icodeN 38 UselessInstance_
    UselessPrivate_                              -> icodeN 39 UselessPrivate_
    AbsurdPatternRequiresNoRHS_                  -> icodeN 40 AbsurdPatternRequiresNoRHS_
    AsPatternShadowsConstructorOrPatternSynonym_ -> icodeN 41 AsPatternShadowsConstructorOrPatternSynonym_
    CantGeneralizeOverSorts_                     -> icodeN 42 CantGeneralizeOverSorts_
    ClashesViaRenaming_                          -> icodeN 43 ClashesViaRenaming_
    CoverageIssue_                               -> icodeN 44 CoverageIssue_
    CoverageNoExactSplit_                        -> icodeN 45 CoverageNoExactSplit_
    DeprecationWarning_                          -> icodeN 46 DeprecationWarning_
    DuplicateUsing_                              -> icodeN 47 DuplicateUsing_
    FixityInRenamingModule_                      -> icodeN 48 FixityInRenamingModule_
    GenericNonFatalError_                        -> icodeN 49 GenericNonFatalError_
    GenericUseless_                              -> icodeN 50 GenericUseless_
    GenericWarning_                              -> icodeN 51 GenericWarning_
    IllformedAsClause_                           -> icodeN 52 IllformedAsClause_
    InstanceArgWithExplicitArg_                  -> icodeN 53 InstanceArgWithExplicitArg_
    InstanceWithExplicitArg_                     -> icodeN 54 InstanceWithExplicitArg_
    InstanceNoOutputTypeName_                    -> icodeN 55 InstanceNoOutputTypeName_
    InversionDepthReached_                       -> icodeN 56 InversionDepthReached_
    ModuleDoesntExport_                          -> icodeN 57 ModuleDoesntExport_
    NoGuardednessFlag_                           -> icodeN 58 NoGuardednessFlag_
    NotInScope_                                  -> icodeN 59 NotInScope_
    NotStrictlyPositive_                         -> icodeN 60 NotStrictlyPositive_
    NoEquivWhenSplitting_                        -> icodeN 61 NoEquivWhenSplitting_
    OldBuiltin_                                  -> icodeN 62 OldBuiltin_
    PragmaCompileErased_                         -> icodeN 63 PragmaCompileErased_
    RewriteMaybeNonConfluent_                    -> icodeN 64 RewriteMaybeNonConfluent_
    RewriteNonConfluent_                         -> icodeN 65 RewriteNonConfluent_
    RewriteAmbiguousRules_                       -> icodeN 66 RewriteAmbiguousRules_
    RewriteMissingRule_                          -> icodeN 67 RewriteMissingRule_
    SafeFlagEta_                                 -> icodeN 68 SafeFlagEta_
    SafeFlagInjective_                           -> icodeN 69 SafeFlagInjective_
    SafeFlagNoCoverageCheck_                     -> icodeN 70 SafeFlagNoCoverageCheck_
    SafeFlagNonTerminating_                      -> icodeN 71 SafeFlagNonTerminating_
    SafeFlagNoPositivityCheck_                   -> icodeN 72 SafeFlagNoPositivityCheck_
    SafeFlagNoUniverseCheck_                     -> icodeN 73 SafeFlagNoUniverseCheck_
    SafeFlagPolarity_                            -> icodeN 74 SafeFlagPolarity_
    SafeFlagPostulate_                           -> icodeN 75 SafeFlagPostulate_
    SafeFlagPragma_                              -> icodeN 76 SafeFlagPragma_
    SafeFlagTerminating_                         -> icodeN 77 SafeFlagTerminating_
    SafeFlagWithoutKFlagPrimEraseEquality_       -> icodeN 78 SafeFlagWithoutKFlagPrimEraseEquality_
    TerminationIssue_                            -> icodeN 79 TerminationIssue_
    UnreachableClauses_                          -> icodeN 80 UnreachableClauses_
    UnsolvedConstraints_                         -> icodeN 81 UnsolvedConstraints_
    UnsolvedInteractionMetas_                    -> icodeN 82 UnsolvedInteractionMetas_
    UnsolvedMetaVariables_                       -> icodeN 83 UnsolvedMetaVariables_
    UselessHiding_                               -> icodeN 84 UselessHiding_
    UselessInline_                               -> icodeN 85 UselessInline_
    UselessPatternDeclarationForRecord_          -> icodeN 86 UselessPatternDeclarationForRecord_
    UselessPublic_                               -> icodeN 87 UselessPublic_
    UserWarning_                                 -> icodeN 88 UserWarning_
    WithoutKFlagPrimEraseEquality_               -> icodeN 89 WithoutKFlagPrimEraseEquality_
    WrongInstanceDeclaration_                    -> icodeN 90 WrongInstanceDeclaration_
    CoInfectiveImport_                           -> icodeN 91 CoInfectiveImport_
    InfectiveImport_                             -> icodeN 92 InfectiveImport_
    DuplicateFieldsWarning_                      -> icodeN 93 DuplicateFieldsWarning_
    TooManyFieldsWarning_                        -> icodeN 94 TooManyFieldsWarning_

  value = vcase $ \case
    [0]  -> valuN OverlappingTokensWarning_
    [1]  -> valuN UnsupportedAttribute_
    [2]  -> valuN MultipleAttributes_
    [3]  -> valuN LibUnknownField_
    [4]  -> valuN EmptyAbstract_
    [5]  -> valuN EmptyConstructor_
    [6]  -> valuN EmptyField_
    [7]  -> valuN EmptyGeneralize_
    [8]  -> valuN EmptyInstance_
    [9]  -> valuN EmptyMacro_
    [10] -> valuN EmptyMutual_
    [11] -> valuN EmptyPostulate_
    [12] -> valuN EmptyPrimitive_
    [13] -> valuN EmptyPrivate_
    [14] -> valuN EmptyRewritePragma_
    [15] -> valuN EmptyWhere_
    [16] -> valuN HiddenGeneralize_
    [17] -> valuN InvalidCatchallPragma_
    [18] -> valuN InvalidConstructor_
    [19] -> valuN InvalidConstructorBlock_
    [20] -> valuN InvalidCoverageCheckPragma_
    [21] -> valuN InvalidNoPositivityCheckPragma_
    [22] -> valuN InvalidNoUniverseCheckPragma_
    [23] -> valuN InvalidRecordDirective_
    [24] -> valuN InvalidTerminationCheckPragma_
    [25] -> valuN MissingDeclarations_
    [26] -> valuN MissingDefinitions_
    [27] -> valuN NotAllowedInMutual_
    [28] -> valuN OpenPublicAbstract_
    [29] -> valuN OpenPublicPrivate_
    [30] -> valuN PolarityPragmasButNotPostulates_
    [31] -> valuN PragmaCompiled_
    [32] -> valuN PragmaNoTerminationCheck_
    [33] -> valuN ShadowingInTelescope_
    [34] -> valuN UnknownFixityInMixfixDecl_
    [35] -> valuN UnknownNamesInFixityDecl_
    [36] -> valuN UnknownNamesInPolarityPragmas_
    [37] -> valuN UselessAbstract_
    [38] -> valuN UselessInstance_
    [39] -> valuN UselessPrivate_
    [40] -> valuN AbsurdPatternRequiresNoRHS_
    [41] -> valuN AsPatternShadowsConstructorOrPatternSynonym_
    [42] -> valuN CantGeneralizeOverSorts_
    [43] -> valuN ClashesViaRenaming_
    [44] -> valuN CoverageIssue_
    [45] -> valuN CoverageNoExactSplit_
    [46] -> valuN DeprecationWarning_
    [47] -> valuN DuplicateUsing_
    [48] -> valuN FixityInRenamingModule_
    [49] -> valuN GenericNonFatalError_
    [50] -> valuN GenericUseless_
    [51] -> valuN GenericWarning_
    [52] -> valuN IllformedAsClause_
    [53] -> valuN InstanceArgWithExplicitArg_
    [54] -> valuN InstanceWithExplicitArg_
    [55] -> valuN InstanceNoOutputTypeName_
    [56] -> valuN InversionDepthReached_
    [57] -> valuN ModuleDoesntExport_
    [58] -> valuN NoGuardednessFlag_
    [59] -> valuN NotInScope_
    [60] -> valuN NotStrictlyPositive_
    [61] -> valuN NoEquivWhenSplitting_
    [62] -> valuN OldBuiltin_
    [63] -> valuN PragmaCompileErased_
    [64] -> valuN RewriteMaybeNonConfluent_
    [65] -> valuN RewriteNonConfluent_
    [66] -> valuN RewriteAmbiguousRules_
    [67] -> valuN RewriteMissingRule_
    [68] -> valuN SafeFlagEta_
    [69] -> valuN SafeFlagInjective_
    [70] -> valuN SafeFlagNoCoverageCheck_
    [71] -> valuN SafeFlagNonTerminating_
    [72] -> valuN SafeFlagNoPositivityCheck_
    [73] -> valuN SafeFlagNoUniverseCheck_
    [74] -> valuN SafeFlagPolarity_
    [75] -> valuN SafeFlagPostulate_
    [76] -> valuN SafeFlagPragma_
    [77] -> valuN SafeFlagTerminating_
    [78] -> valuN SafeFlagWithoutKFlagPrimEraseEquality_
    [79] -> valuN TerminationIssue_
    [80] -> valuN UnreachableClauses_
    [81] -> valuN UnsolvedConstraints_
    [82] -> valuN UnsolvedInteractionMetas_
    [83] -> valuN UnsolvedMetaVariables_
    [84] -> valuN UselessHiding_
    [85] -> valuN UselessInline_
    [86] -> valuN UselessPatternDeclarationForRecord_
    [87] -> valuN UselessPublic_
    [88] -> valuN UserWarning_
    [89] -> valuN WithoutKFlagPrimEraseEquality_
    [90] -> valuN WrongInstanceDeclaration_
    [91] -> valuN CoInfectiveImport_
    [92] -> valuN InfectiveImport_
    [93] -> valuN DuplicateFieldsWarning_
    [94] -> valuN TooManyFieldsWarning_
    _ -> malformed


instance EmbPrj CutOff where
  icod_ = \case
    DontCutOff -> icodeN' DontCutOff
    CutOff a -> icodeN 0 CutOff a

  value = vcase valu where
    valu [] = valuN DontCutOff
    valu [0,a] = valuN CutOff a
    valu _ = malformed
