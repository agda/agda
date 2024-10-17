{-# OPTIONS_GHC -fno-warn-orphans     #-}

module Agda.TypeChecking.Serialise.Instances.Errors where

import Control.Monad

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common   ( SerialisedRange(..) )
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

instance EmbPrj IsAmbiguous where
  icod_ = \case
    YesAmbiguous a -> icodeN' YesAmbiguous a
    NotAmbiguous   -> icodeN' NotAmbiguous

  value = vcase \case
    [a] -> valuN YesAmbiguous a
    []  -> valuN NotAmbiguous
    _   -> malformed

instance EmbPrj TCWarning where
  icod_ (TCWarning fp r a b c d) = icodeN' (\ fp -> TCWarning fp . underlyingRange) fp (SerialisedRange r) a b c d
  value = valueN (\ fp -> TCWarning fp . underlyingRange)

-- We don't need to serialise warnings that turn into errors
instance EmbPrj Warning where
  icod_ = \case
    TerminationIssue a                    -> __IMPOSSIBLE__
    UnreachableClauses a b                -> icodeN 0 UnreachableClauses a b
    CoverageIssue a b                     -> __IMPOSSIBLE__
    NotStrictlyPositive a b               -> __IMPOSSIBLE__
    ConstructorDoesNotFitInData{}         -> __IMPOSSIBLE__
    UnsolvedMetaVariables a               -> __IMPOSSIBLE__
    UnsolvedInteractionMetas a            -> __IMPOSSIBLE__
    UnsolvedConstraints a                 -> __IMPOSSIBLE__
    InteractionMetaBoundaries a           -> __IMPOSSIBLE__
    OldBuiltin a b                        -> icodeN 1 OldBuiltin a b
    EmptyRewritePragma                    -> icodeN 2 EmptyRewritePragma
    UselessPublic                         -> icodeN 3 UselessPublic
    UselessInline a                       -> icodeN 4 UselessInline a
    InvalidCharacterLiteral a             -> __IMPOSSIBLE__
    SafeFlagPostulate a                   -> __IMPOSSIBLE__
    SafeFlagPragma a                      -> __IMPOSSIBLE__
    SafeFlagWithoutKFlagPrimEraseEquality -> __IMPOSSIBLE__
    DuplicateRecordDirective a            -> icodeN 5 DuplicateRecordDirective a
    DeprecationWarning a b c              -> icodeN 6 DeprecationWarning a b c
    NicifierIssue a                       -> icodeN 7 NicifierIssue a
    InversionDepthReached a               -> icodeN 8 InversionDepthReached a
    UserWarning a                         -> icodeN 9 UserWarning a
    AbsurdPatternRequiresAbsentRHS        -> icodeN 10 AbsurdPatternRequiresAbsentRHS
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
    NotInScopeW a                         -> icodeN 27 NotInScopeW a
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
    -- Not source code related, therefore they should never be serialized
    DuplicateInterfaceFiles a b           -> __IMPOSSIBLE__
    ConfluenceCheckingIncompleteBecauseOfMeta a -> icodeN 50 ConfluenceCheckingIncompleteBecauseOfMeta a
    BuiltinDeclaresIdentifier a                 -> icodeN 51 BuiltinDeclaresIdentifier a
    ConfluenceForCubicalNotSupported            -> icodeN 52 ConfluenceForCubicalNotSupported
    -- We do not need to serialize compiler warnings:
    PragmaCompileList                           -> __IMPOSSIBLE__
    PragmaCompileMaybe                          -> __IMPOSSIBLE__
    NoMain _                                    -> __IMPOSSIBLE__
    IllegalRewriteRule a b                      -> icodeN 53 IllegalRewriteRule a b
    MissingTypeSignatureForOpaque a b           -> icodeN 54 MissingTypeSignatureForOpaque a b
    ConflictingPragmaOptions a b                -> icodeN 55 ConflictingPragmaOptions a b
    CustomBackendWarning a b                    -> icodeN 56 CustomBackendWarning a b
    CoinductiveEtaRecord a                      -> icodeN 57 CoinductiveEtaRecord a
    WithClauseProjectionFixityMismatch a b c d  -> icodeN 58 WithClauseProjectionFixityMismatch a b c d
    InvalidDisplayForm a b                      -> icodeN 59 InvalidDisplayForm a b
    TooManyArgumentsToSort a b                  -> __IMPOSSIBLE__
    NotARewriteRule a b                         -> icodeN 60 NotARewriteRule a b
    PragmaCompileWrongName a b                  -> icodeN 61 PragmaCompileWrongName a b
    PragmaCompileUnparsable a                   -> icodeN 62 PragmaCompileUnparsable a
    PragmaCompileWrong a b                      -> icodeN 63 PragmaCompileWrong a b
    PragmaExpectsUnambiguousConstructorOrFunction a b c ->
      icodeN 64 PragmaExpectsUnambiguousConstructorOrFunction a b c
    PragmaExpectsUnambiguousProjectionOrFunction a b c ->
      icodeN 65 PragmaExpectsUnambiguousProjectionOrFunction a b c
    PragmaExpectsDefinedSymbol a b              -> icodeN 66 PragmaExpectsDefinedSymbol a b
    UnfoldingWrongName a                        -> icodeN 67 UnfoldingWrongName a
    -- TODO: linearity
    -- FixingQuantity a b c                        -> icodeN 68 FixingQuantity a b c
    FixingRelevance a b c                       -> icodeN 69 FixingRelevance a b c
    UnusedVariablesInDisplayForm a              -> icodeN 70 UnusedVariablesInDisplayForm a
    HiddenNotInArgumentPosition a               -> __IMPOSSIBLE__
    InstanceNotInArgumentPosition a             -> __IMPOSSIBLE__

  value = vcase $ \ case
    [0, a, b]            -> valuN UnreachableClauses a b
    [1, a, b]            -> valuN OldBuiltin a b
    [2]                  -> valuN EmptyRewritePragma
    [3]                  -> valuN UselessPublic
    [4, a]               -> valuN UselessInline a
    [5, a]               -> valuN DuplicateRecordDirective a
    [6, a, b, c]         -> valuN DeprecationWarning a b c
    [7, a]               -> valuN NicifierIssue a
    [8, a]               -> valuN InversionDepthReached a
    [9, a]               -> valuN UserWarning a
    [10]                 -> valuN AbsurdPatternRequiresAbsentRHS
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
    [27, a]              -> valuN NotInScopeW a
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
    [50, a]              -> valuN ConfluenceCheckingIncompleteBecauseOfMeta a
    [51, a]              -> valuN BuiltinDeclaresIdentifier a
    [52]                 -> valuN ConfluenceForCubicalNotSupported
    [53, a, b]           -> valuN IllegalRewriteRule a b
    [54, a, b]           -> valuN MissingTypeSignatureForOpaque a b
    [55, a, b]           -> valuN ConflictingPragmaOptions a b
    [56, a, b]           -> valuN CustomBackendWarning a b
    [57, a]              -> valuN CoinductiveEtaRecord a
    [58, a, b, c, d]     -> valuN WithClauseProjectionFixityMismatch a b c d
    [59, a, b]           -> valuN InvalidDisplayForm a b
    [60, a, b]           -> valuN NotARewriteRule a b
    [61, a, b]           -> valuN PragmaCompileWrongName a b
    [62, a]              -> valuN PragmaCompileUnparsable a
    [63, a, b]           -> valuN PragmaCompileWrong a b
    [64, a, b, c]        -> valuN PragmaExpectsUnambiguousConstructorOrFunction a b c
    [65, a, b, c]        -> valuN PragmaExpectsUnambiguousProjectionOrFunction a b c
    [66, a, b]           -> valuN PragmaExpectsDefinedSymbol a b
    [67, a]              -> valuN UnfoldingWrongName a
    -- TODO: linearity
    -- [68, a, b, c]        -> valuN FixingQuantity a b c
    [69, a, b, c]        -> valuN FixingRelevance a b c
    [70, a]              -> valuN UnusedVariablesInDisplayForm a
    _ -> malformed

instance EmbPrj IllegalRewriteRuleReason where
  icod_ = \case
    LHSNotDefinitionOrConstructor               -> icodeN 0 LHSNotDefinitionOrConstructor
    VariablesNotBoundByLHS a                    -> icodeN 1 VariablesNotBoundByLHS a
    VariablesBoundMoreThanOnce a                -> icodeN 2 VariablesBoundMoreThanOnce a
    LHSReduces a b                              -> icodeN 3 LHSReduces a b
    -- 4 was HeadSymbolIsProjection
    HeadSymbolIsProjectionLikeFunction a        -> icodeN 5 HeadSymbolIsProjectionLikeFunction a
    HeadSymbolIsTypeConstructor a               -> icodeN 6 HeadSymbolIsTypeConstructor a
    HeadSymbolContainsMetas a                   -> icodeN 7 HeadSymbolContainsMetas a
    ConstructorParametersNotGeneral a b         -> icodeN 8 ConstructorParametersNotGeneral a b
    ContainsUnsolvedMetaVariables a             -> icodeN 9 ContainsUnsolvedMetaVariables a
    BlockedOnProblems a                         -> icodeN 10 BlockedOnProblems a
    RequiresDefinitions a                       -> icodeN 11 RequiresDefinitions a
    DoesNotTargetRewriteRelation                -> icodeN 12 DoesNotTargetRewriteRelation
    BeforeFunctionDefinition                    -> icodeN 13 BeforeFunctionDefinition
    BeforeMutualFunctionDefinition a            -> icodeN 14 BeforeMutualFunctionDefinition a
    DuplicateRewriteRule                        -> icodeN 15 DuplicateRewriteRule

  value = vcase $ \case
    [0]       -> valuN LHSNotDefinitionOrConstructor
    [1, a]    -> valuN VariablesNotBoundByLHS a
    [2, a]    -> valuN VariablesBoundMoreThanOnce a
    [3, a, b] -> valuN LHSReduces a b
    -- 4 was HeadSymbolIsProjection
    [5, a]    -> valuN HeadSymbolIsProjectionLikeFunction a
    [6, a]    -> valuN HeadSymbolIsTypeConstructor a
    [7, a]    -> valuN HeadSymbolContainsMetas a
    [8, a, b] -> valuN ConstructorParametersNotGeneral a b
    [9, a]    -> valuN ContainsUnsolvedMetaVariables a
    [10, a]   -> valuN BlockedOnProblems a
    [11, a]   -> valuN RequiresDefinitions a
    [12]      -> valuN DoesNotTargetRewriteRelation
    [13]      -> valuN BeforeFunctionDefinition
    [14, a]   -> valuN BeforeMutualFunctionDefinition a
    [15]      -> valuN DuplicateRewriteRule
    _ -> malformed

instance EmbPrj OptionWarning where
  icod_ = \case
    OptionRenamed a b -> icodeN 0 OptionRenamed a b
    WarningProblem a  -> icodeN 1 WarningProblem a

  value = vcase $ \case
    [0, a, b] -> valuN OptionRenamed a b
    [1, a]    -> valuN WarningProblem a
    _ -> malformed

instance EmbPrj WarningModeError where
  icod_ = \case
    Unknown a   -> icodeN 0 Unknown a
    NoNoError a -> icodeN 1 NoNoError a

  value = vcase $ \case
    [0, a] -> valuN Unknown a
    [1, a] -> valuN NoNoError a
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
    -- 29 removed
    -- 30 removed
    InvalidConstructorBlock a         -> icodeN 31 InvalidConstructorBlock a
    MissingDataDeclaration a          -> icodeN 32 MissingDataDeclaration a
    HiddenGeneralize r                -> icodeN 33 HiddenGeneralize r
    UselessMacro r                    -> icodeN 34 UselessMacro r
    SafeFlagEta                    {} -> __IMPOSSIBLE__
    SafeFlagInjective              {} -> __IMPOSSIBLE__
    SafeFlagNoCoverageCheck        {} -> __IMPOSSIBLE__
    SafeFlagNoPositivityCheck      {} -> __IMPOSSIBLE__
    SafeFlagNoUniverseCheck        {} -> __IMPOSSIBLE__
    SafeFlagNonTerminating         {} -> __IMPOSSIBLE__
    SafeFlagPolarity               {} -> __IMPOSSIBLE__
    SafeFlagTerminating            {} -> __IMPOSSIBLE__
    EmptyPolarityPragma r             -> icodeN 35 EmptyPolarityPragma r

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
    -- 29 removed
    -- 30 removed
    [31,r]   -> valuN InvalidConstructorBlock r
    [32,r]   -> valuN MissingDataDeclaration r
    [33,r]   -> valuN HiddenGeneralize r
    [34,r]   -> valuN UselessMacro r
    [35,r]   -> valuN EmptyPolarityPragma r
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

instance EmbPrj ProfileOption

instance EmbPrj LHSOrPatSyn

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

-- Andreas, 2024-08-18
-- Removed manual implementation of EmbPrj for this Enum type.
instance EmbPrj WarningName

instance EmbPrj CutOff where
  icod_ = \case
    DontCutOff -> icodeN' DontCutOff
    CutOff a -> icodeN 0 CutOff a

  value = vcase valu where
    valu [] = valuN DontCutOff
    valu [0,a] = valuN CutOff a
    valu _ = malformed
