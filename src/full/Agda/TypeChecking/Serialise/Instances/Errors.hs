{-# OPTIONS_GHC -fno-warn-orphans     #-}

module Agda.TypeChecking.Serialise.Instances.Errors where

import Control.Monad

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Internal () --instance only
import Agda.TypeChecking.Serialise.Instances.Abstract () --instance only

import Agda.Syntax.Concrete.Definitions (DeclarationWarning(..), DeclarationWarning'(..))
import Agda.Syntax.Parser.Monad
import Agda.TypeChecking.Monad.Base
import qualified Agda.TypeChecking.Monad.Base.Warning as W
import Agda.Interaction.Options
import Agda.Interaction.Options.Warnings
import Agda.Interaction.Library.Base
import Agda.Termination.CutOff
import Agda.Syntax.Common.Pretty
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
    InteractionMetaBoundaries a           -> __IMPOSSIBLE__
    OldBuiltin a b                        -> icodeN 1 OldBuiltin a b
    EmptyRewritePragma                    -> icodeN 2 EmptyRewritePragma
    UselessPublic                         -> icodeN 3 UselessPublic
    UselessInline a                       -> icodeN 4 UselessInline a
    GenericWarning a                      -> icodeN 5 GenericWarning a
    InvalidCharacterLiteral a             -> __IMPOSSIBLE__
    SafeFlagPostulate a                   -> __IMPOSSIBLE__
    SafeFlagPragma a                      -> __IMPOSSIBLE__
    SafeFlagWithoutKFlagPrimEraseEquality -> __IMPOSSIBLE__
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
    InfectiveImport a                     -> icodeN 18 InfectiveImport a
    CoInfectiveImport a                   -> icodeN 19 CoInfectiveImport a
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
    UselessPragma a b                     -> icodeN 35 UselessPragma a b
    RewriteAmbiguousRules a b c           -> icodeN 36 RewriteAmbiguousRules a b c
    RewriteMissingRule a b c              -> icodeN 37 RewriteMissingRule a b c
    ParseWarning a                        -> icodeN 38 ParseWarning a
    NoGuardednessFlag a                   -> icodeN 39 NoGuardednessFlag a
    UnsupportedIndexedMatch f             -> icodeN 40 UnsupportedIndexedMatch f
    OptionWarning a                       -> icodeN 41 OptionWarning a
    PlentyInHardCompileTimeMode a         -> icodeN 42 PlentyInHardCompileTimeMode a
    NotAffectedByOpaque                   -> icodeN 43 NotAffectedByOpaque
    UnfoldTransparentName nm              -> icodeN 44 UnfoldTransparentName nm
    UselessOpaque                         -> icodeN 45 UselessOpaque
    InlineNoExactSplit a b                -> icodeN 46 InlineNoExactSplit a b
    FaceConstraintCannotBeHidden a        -> icodeN 47 FaceConstraintCannotBeHidden a
    FaceConstraintCannotBeNamed a         -> icodeN 48 FaceConstraintCannotBeNamed a
    PatternShadowsConstructor a b         -> icodeN 49 PatternShadowsConstructor a b

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
    [18, a]              -> valuN InfectiveImport a
    [19, a]              -> valuN CoInfectiveImport a
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
    [35, a, b]           -> valuN UselessPragma a b
    [36, a, b, c]        -> valuN RewriteAmbiguousRules a b c
    [37, a, b, c]        -> valuN RewriteMissingRule a b c
    [38, a]              -> valuN ParseWarning a
    [39, a]              -> valuN NoGuardednessFlag a
    [40, a]              -> valuN UnsupportedIndexedMatch a
    [41, a]              -> valuN OptionWarning a
    [42, a]              -> valuN PlentyInHardCompileTimeMode a
    [43]                 -> valuN NotAffectedByOpaque
    [44, a]              -> valuN UnfoldTransparentName a
    [45]                 -> valuN UselessOpaque
    [46, a, b]           -> valuN InlineNoExactSplit a b
    [47, a]              -> valuN FaceConstraintCannotBeHidden a
    [48, a]              -> valuN FaceConstraintCannotBeNamed a
    [49, a, b]           -> valuN PatternShadowsConstructor a b
    _ -> malformed

instance EmbPrj OptionWarning where
  icod_ = \case
    OptionRenamed a b -> icodeN' OptionRenamed a b

  value = vcase $ \case
    [a, b] -> valuN OptionRenamed a b
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
    W.DuplicateFields a   -> icodeN 0 W.DuplicateFields a
    W.TooManyFields a b c -> icodeN 1 W.TooManyFields a b c

  value = vcase $ \case
    [0, a]       -> valuN W.DuplicateFields a
    [1, a, b, c] -> valuN W.TooManyFields a b c
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
    SafeFlagEta                    {} -> __IMPOSSIBLE__
    SafeFlagInjective              {} -> __IMPOSSIBLE__
    SafeFlagNoCoverageCheck        {} -> __IMPOSSIBLE__
    SafeFlagNoPositivityCheck      {} -> __IMPOSSIBLE__
    SafeFlagNoUniverseCheck        {} -> __IMPOSSIBLE__
    SafeFlagNonTerminating         {} -> __IMPOSSIBLE__
    SafeFlagPolarity               {} -> __IMPOSSIBLE__
    SafeFlagTerminating            {} -> __IMPOSSIBLE__

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

instance EmbPrj InfectiveCoinfective where
  icod_ Infective   = icodeN' Infective
  icod_ Coinfective = icodeN 0 Coinfective

  value = vcase valu where
    valu []  = valuN Infective
    valu [0] = valuN Coinfective
    valu _   = malformed

instance EmbPrj PragmaOptions where
  icod_    (PragmaOptions a b c d e f g h i j k l m n o p q r s t u v w x y z aa bb cc dd ee ff gg hh ii jj kk ll mm nn oo pp qq rr ss tt uu vv ww xx yy zz aaa bbb ccc ddd eee fff ggg hhh iii jjj kkk lll mmm nnn ooo ppp qqq rrr) =
    icodeN' PragmaOptions a b c d e f g h i j k l m n o p q r s t u v w x y z aa bb cc dd ee ff gg hh ii jj kk ll mm nn oo pp qq rr ss tt uu vv ww xx yy zz aaa bbb ccc ddd eee fff ggg hhh iii jjj kkk lll mmm nnn ooo ppp qqq rrr

  value = valueN PragmaOptions

instance EmbPrj ProfileOptions where
  icod_ opts = icode (profileOptionsToList opts)
  value = fmap profileOptionsFromList . value

instance EmbPrj ProfileOption where

instance EmbPrj UnicodeOrAscii

instance EmbPrj ConfluenceCheck where
  icod_ LocalConfluenceCheck  = icodeN' LocalConfluenceCheck
  icod_ GlobalConfluenceCheck = icodeN 0 GlobalConfluenceCheck

  value = vcase valu where
    valu []  = valuN LocalConfluenceCheck
    valu [0] = valuN GlobalConfluenceCheck
    valu _   = malformed

instance EmbPrj WarningMode where
  icod_ (WarningMode a b) = icodeN' WarningMode a b

  value = valueN WarningMode

instance EmbPrj WarningName where
  icod_ = return . \case
    OverlappingTokensWarning_                    -> 0
    UnsupportedAttribute_                        -> 1
    MultipleAttributes_                          -> 2
    LibUnknownField_                             -> 3
    EmptyAbstract_                               -> 4
    EmptyConstructor_                            -> 5
    EmptyField_                                  -> 6
    EmptyGeneralize_                             -> 7
    EmptyInstance_                               -> 8
    EmptyMacro_                                  -> 9
    EmptyMutual_                                 -> 10
    EmptyPostulate_                              -> 11
    EmptyPrimitive_                              -> 12
    EmptyPrivate_                                -> 13
    EmptyRewritePragma_                          -> 14
    EmptyWhere_                                  -> 15
    HiddenGeneralize_                            -> 16
    InvalidCatchallPragma_                       -> 17
    InvalidConstructor_                          -> 18
    InvalidConstructorBlock_                     -> 19
    InvalidCoverageCheckPragma_                  -> 20
    InvalidNoPositivityCheckPragma_              -> 21
    InvalidNoUniverseCheckPragma_                -> 22
    InvalidRecordDirective_                      -> 23
    InvalidTerminationCheckPragma_               -> 24
    MissingDeclarations_                         -> 25
    MissingDefinitions_                          -> 26
    NotAllowedInMutual_                          -> 27
    OpenPublicAbstract_                          -> 28
    OpenPublicPrivate_                           -> 29
    PolarityPragmasButNotPostulates_             -> 30
    PragmaCompiled_                              -> 31
    PragmaNoTerminationCheck_                    -> 32
    ShadowingInTelescope_                        -> 33
    UnknownFixityInMixfixDecl_                   -> 34
    UnknownNamesInFixityDecl_                    -> 35
    UnknownNamesInPolarityPragmas_               -> 36
    UselessAbstract_                             -> 37
    UselessInstance_                             -> 38
    UselessPrivate_                              -> 39
    AbsurdPatternRequiresNoRHS_                  -> 40
    AsPatternShadowsConstructorOrPatternSynonym_ -> 41
    CantGeneralizeOverSorts_                     -> 42
    ClashesViaRenaming_                          -> 43
    CoverageIssue_                               -> 44
    CoverageNoExactSplit_                        -> 45
    DeprecationWarning_                          -> 46
    DuplicateUsing_                              -> 47
    FixityInRenamingModule_                      -> 48
    InvalidCharacterLiteral_                     -> 49
    UselessPragma_                               -> 50
    GenericWarning_                              -> 51
    IllformedAsClause_                           -> 52
    InstanceArgWithExplicitArg_                  -> 53
    InstanceWithExplicitArg_                     -> 54
    InstanceNoOutputTypeName_                    -> 55
    InversionDepthReached_                       -> 56
    ModuleDoesntExport_                          -> 57
    NoGuardednessFlag_                           -> 58
    NotInScope_                                  -> 59
    NotStrictlyPositive_                         -> 60
    UnsupportedIndexedMatch_                     -> 61
    OldBuiltin_                                  -> 62
    PragmaCompileErased_                         -> 63
    RewriteMaybeNonConfluent_                    -> 64
    RewriteNonConfluent_                         -> 65
    RewriteAmbiguousRules_                       -> 66
    RewriteMissingRule_                          -> 67
    SafeFlagEta_                                 -> 68
    SafeFlagInjective_                           -> 69
    SafeFlagNoCoverageCheck_                     -> 70
    SafeFlagNonTerminating_                      -> 71
    SafeFlagNoPositivityCheck_                   -> 72
    SafeFlagNoUniverseCheck_                     -> 73
    SafeFlagPolarity_                            -> 74
    SafeFlagPostulate_                           -> 75
    SafeFlagPragma_                              -> 76
    SafeFlagTerminating_                         -> 77
    SafeFlagWithoutKFlagPrimEraseEquality_       -> 78
    TerminationIssue_                            -> 79
    UnreachableClauses_                          -> 80
    UnsolvedConstraints_                         -> 81
    UnsolvedInteractionMetas_                    -> 82
    UnsolvedMetaVariables_                       -> 83
    UselessHiding_                               -> 84
    UselessInline_                               -> 85
    UselessPatternDeclarationForRecord_          -> 86
    UselessPublic_                               -> 87
    UserWarning_                                 -> 88
    WithoutKFlagPrimEraseEquality_               -> 89
    WrongInstanceDeclaration_                    -> 90
    CoInfectiveImport_                           -> 91
    InfectiveImport_                             -> 92
    DuplicateFields_                             -> 93
    TooManyFields_                               -> 94
    OptionRenamed_                               -> 95
    PlentyInHardCompileTimeMode_                 -> 96
    InteractionMetaBoundaries_                   -> 97
    NotAffectedByOpaque_                         -> 98
    UnfoldTransparentName_                       -> 99
    UselessOpaque_                               -> 100
    InlineNoExactSplit_                          -> 101
    FaceConstraintCannotBeHidden_                -> 102
    FaceConstraintCannotBeNamed_                 -> 103
    PatternShadowsConstructor_                   -> 104

  value = \case
    0   -> return OverlappingTokensWarning_
    1   -> return UnsupportedAttribute_
    2   -> return MultipleAttributes_
    3   -> return LibUnknownField_
    4   -> return EmptyAbstract_
    5   -> return EmptyConstructor_
    6   -> return EmptyField_
    7   -> return EmptyGeneralize_
    8   -> return EmptyInstance_
    9   -> return EmptyMacro_
    10  -> return EmptyMutual_
    11  -> return EmptyPostulate_
    12  -> return EmptyPrimitive_
    13  -> return EmptyPrivate_
    14  -> return EmptyRewritePragma_
    15  -> return EmptyWhere_
    16  -> return HiddenGeneralize_
    17  -> return InvalidCatchallPragma_
    18  -> return InvalidConstructor_
    19  -> return InvalidConstructorBlock_
    20  -> return InvalidCoverageCheckPragma_
    21  -> return InvalidNoPositivityCheckPragma_
    22  -> return InvalidNoUniverseCheckPragma_
    23  -> return InvalidRecordDirective_
    24  -> return InvalidTerminationCheckPragma_
    25  -> return MissingDeclarations_
    26  -> return MissingDefinitions_
    27  -> return NotAllowedInMutual_
    28  -> return OpenPublicAbstract_
    29  -> return OpenPublicPrivate_
    30  -> return PolarityPragmasButNotPostulates_
    31  -> return PragmaCompiled_
    32  -> return PragmaNoTerminationCheck_
    33  -> return ShadowingInTelescope_
    34  -> return UnknownFixityInMixfixDecl_
    35  -> return UnknownNamesInFixityDecl_
    36  -> return UnknownNamesInPolarityPragmas_
    37  -> return UselessAbstract_
    38  -> return UselessInstance_
    39  -> return UselessPrivate_
    40  -> return AbsurdPatternRequiresNoRHS_
    41  -> return AsPatternShadowsConstructorOrPatternSynonym_
    42  -> return CantGeneralizeOverSorts_
    43  -> return ClashesViaRenaming_
    44  -> return CoverageIssue_
    45  -> return CoverageNoExactSplit_
    46  -> return DeprecationWarning_
    47  -> return DuplicateUsing_
    48  -> return FixityInRenamingModule_
    49  -> return InvalidCharacterLiteral_
    50  -> return UselessPragma_
    51  -> return GenericWarning_
    52  -> return IllformedAsClause_
    53  -> return InstanceArgWithExplicitArg_
    54  -> return InstanceWithExplicitArg_
    55  -> return InstanceNoOutputTypeName_
    56  -> return InversionDepthReached_
    57  -> return ModuleDoesntExport_
    58  -> return NoGuardednessFlag_
    59  -> return NotInScope_
    60  -> return NotStrictlyPositive_
    61  -> return UnsupportedIndexedMatch_
    62  -> return OldBuiltin_
    63  -> return PragmaCompileErased_
    64  -> return RewriteMaybeNonConfluent_
    65  -> return RewriteNonConfluent_
    66  -> return RewriteAmbiguousRules_
    67  -> return RewriteMissingRule_
    68  -> return SafeFlagEta_
    69  -> return SafeFlagInjective_
    70  -> return SafeFlagNoCoverageCheck_
    71  -> return SafeFlagNonTerminating_
    72  -> return SafeFlagNoPositivityCheck_
    73  -> return SafeFlagNoUniverseCheck_
    74  -> return SafeFlagPolarity_
    75  -> return SafeFlagPostulate_
    76  -> return SafeFlagPragma_
    77  -> return SafeFlagTerminating_
    78  -> return SafeFlagWithoutKFlagPrimEraseEquality_
    79  -> return TerminationIssue_
    80  -> return UnreachableClauses_
    81  -> return UnsolvedConstraints_
    82  -> return UnsolvedInteractionMetas_
    83  -> return UnsolvedMetaVariables_
    84  -> return UselessHiding_
    85  -> return UselessInline_
    86  -> return UselessPatternDeclarationForRecord_
    87  -> return UselessPublic_
    88  -> return UserWarning_
    89  -> return WithoutKFlagPrimEraseEquality_
    90  -> return WrongInstanceDeclaration_
    91  -> return CoInfectiveImport_
    92  -> return InfectiveImport_
    93  -> return DuplicateFields_
    94  -> return TooManyFields_
    95  -> return OptionRenamed_
    96  -> return PlentyInHardCompileTimeMode_
    97  -> return InteractionMetaBoundaries_
    98  -> return NotAffectedByOpaque_
    99  -> return UnfoldTransparentName_
    100 -> return UselessOpaque_
    101 -> return InlineNoExactSplit_
    102 -> return FaceConstraintCannotBeHidden_
    103 -> return FaceConstraintCannotBeNamed_
    104 -> return PatternShadowsConstructor_
    _   -> malformed


instance EmbPrj CutOff where
  icod_ = \case
    DontCutOff -> icodeN' DontCutOff
    CutOff a -> icodeN 0 CutOff a

  value = vcase valu where
    valu [] = valuN DontCutOff
    valu [0,a] = valuN CutOff a
    valu _ = malformed
