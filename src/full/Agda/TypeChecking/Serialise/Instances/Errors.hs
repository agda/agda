
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Serialise.Instances.Errors where

import Control.Monad

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common   ( SerialisedRange(..) )
import Agda.TypeChecking.Serialise.Instances.General  () --instance only
import Agda.TypeChecking.Serialise.Instances.Abstract () --instance only
import Agda.TypeChecking.Serialise.Instances.Internal () --instance only
import Agda.TypeChecking.Serialise.Instances.Highlighting () --instance only

import Agda.Syntax.Common.Pretty
import Agda.Syntax.Concrete.Definitions.Errors
    ( DeclarationWarning(..), DeclarationWarning'(..), OpenOrImport(..) )
import Agda.Syntax.Parser.Monad
import Agda.TypeChecking.Monad.Base
import qualified Agda.TypeChecking.Monad.Base.Warning as W
import Agda.Interaction.Options
import Agda.Interaction.Options.ProfileOptions
import Agda.Interaction.Options.Warnings
import Agda.Interaction.Library.Base
import Agda.Termination.CutOff

import Agda.Utils.DocTree qualified as DocTree
import Agda.Utils.Impossible

instance EmbPrj IsAmbiguous where
  icod_ = \case
    YesAmbiguous a -> icodeN' YesAmbiguous a
    NotAmbiguous   -> icodeN' NotAmbiguous

  value = vcase \case
    N1 a -> valuN YesAmbiguous a
    N0   -> valuN NotAmbiguous
    _    -> malformed

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
    UselessPublic a                       -> icodeN 3 UselessPublic a
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
    UselessTactic                         -> icodeN 39 UselessTactic
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
    ConfluenceCheckingIncompleteBecauseOfMeta a -> icodeN 50 ConfluenceCheckingIncompleteBecauseOfMeta a
    BuiltinDeclaresIdentifier a                 -> icodeN 51 BuiltinDeclaresIdentifier a
    ConfluenceForCubicalNotSupported            -> icodeN 52 ConfluenceForCubicalNotSupported
    -- We do not need to serialize compiler warnings:
    PragmaCompileList                           -> __IMPOSSIBLE__
    PragmaCompileMaybe                          -> __IMPOSSIBLE__
    NoMain _                                    -> __IMPOSSIBLE__
    UnknownJSPrimitive _                        -> __IMPOSSIBLE__
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
    MacroInLetBindings                          -> __IMPOSSIBLE__
    AbstractInLetBindings                       -> __IMPOSSIBLE__
    TopLevelPolarity a b                        -> __IMPOSSIBLE__
    TooManyPolarities a b                       -> icodeN 71 TooManyPolarities a b
    FixingCohesion a b c                        -> icodeN 72 FixingCohesion a b c
    FixingPolarity a b c                        -> icodeN 73 FixingPolarity a b c
    RewritesNothing                             -> icodeN 74 RewritesNothing
    IllegalDeclarationInDataDefinition ds       -> __IMPOSSIBLE__  -- We don't serialize concrete definitions (yet)
    UnusedImports a b                           -> icodeN 75 UnusedImports a b

  value = vcase $ \ case
    N3 0 a b      -> valuN UnreachableClauses a b
    N3 1 a b      -> valuN OldBuiltin a b
    N1 2          -> valuN EmptyRewritePragma
    N2 3 a        -> valuN UselessPublic a
    N2 4 a        -> valuN UselessInline a
    N2 5 a        -> valuN DuplicateRecordDirective a
    N4 6 a b c    -> valuN DeprecationWarning a b c
    N2 7 a        -> valuN NicifierIssue a
    N2 8 a        -> valuN InversionDepthReached a
    N2 9 a        -> valuN UserWarning a
    N1 10         -> valuN AbsurdPatternRequiresAbsentRHS
    N5 11 a b c d -> valuN ModuleDoesntExport a b c d
    N2 12 a       -> valuN LibraryWarning a
    N3 13 a b     -> valuN CoverageNoExactSplit a b
    N2 14 a       -> valuN CantGeneralizeOverSorts a
    N2 15 a       -> valuN IllformedAsClause a
    N1 16         -> valuN WithoutKFlagPrimEraseEquality
    N2 17 a       -> valuN InstanceWithExplicitArg a
    N2 18 a       -> valuN InfectiveImport a
    N2 19 a       -> valuN CoInfectiveImport a
    N2 20 a       -> valuN InstanceNoOutputTypeName a
    N2 21 a       -> valuN InstanceArgWithExplicitArg a
    N1 22         -> valuN WrongInstanceDeclaration
    N5 23 a b c d -> valuN RewriteNonConfluent a b c d
    N4 24 a b c   -> valuN RewriteMaybeNonConfluent a b c
    N3 25 a b     -> valuN PragmaCompileErased a b
    N2 26 a       -> valuN FixityInRenamingModule a
    N2 27 a       -> valuN NotInScopeW a
    N3 28 a b     -> valuN ClashesViaRenaming a b
    N2 29 a       -> valuN RecordFieldWarning a
    N2 30 a       -> valuN UselessPatternDeclarationForRecord a
    N1 31         -> valuN EmptyWhere
    N2 32 a       -> valuN AsPatternShadowsConstructorOrPatternSynonym a
    N2 33 a       -> valuN DuplicateUsing a
    N2 34 a       -> valuN UselessHiding a
    N3 35 a b     -> valuN UselessPragma a b
    N4 36 a b c   -> valuN RewriteAmbiguousRules a b c
    N4 37 a b c   -> valuN RewriteMissingRule a b c
    N2 38 a       -> valuN ParseWarning a
    N1 39         -> valuN UselessTactic
    N2 40 a       -> valuN UnsupportedIndexedMatch a
    N2 41 a       -> valuN OptionWarning a
    N2 42 a       -> valuN PlentyInHardCompileTimeMode a
    N1 43         -> valuN NotAffectedByOpaque
    N2 44 a       -> valuN UnfoldTransparentName a
    N1 45         -> valuN UselessOpaque
    N3 46 a b     -> valuN InlineNoExactSplit a b
    N2 47 a       -> valuN FaceConstraintCannotBeHidden a
    N2 48 a       -> valuN FaceConstraintCannotBeNamed a
    N3 49 a b     -> valuN PatternShadowsConstructor a b
    N2 50 a       -> valuN ConfluenceCheckingIncompleteBecauseOfMeta a
    N2 51 a       -> valuN BuiltinDeclaresIdentifier a
    N1 52         -> valuN ConfluenceForCubicalNotSupported
    N3 53 a b     -> valuN IllegalRewriteRule a b
    N3 54 a b     -> valuN MissingTypeSignatureForOpaque a b
    N3 55 a b     -> valuN ConflictingPragmaOptions a b
    N3 56 a b     -> valuN CustomBackendWarning a b
    N2 57 a       -> valuN CoinductiveEtaRecord a
    N5 58 a b c d -> valuN WithClauseProjectionFixityMismatch a b c d
    N3 59 a b     -> valuN InvalidDisplayForm a b
    N3 60 a b     -> valuN NotARewriteRule a b
    N3 61 a b     -> valuN PragmaCompileWrongName a b
    N2 62 a       -> valuN PragmaCompileUnparsable a
    N3 63 a b     -> valuN PragmaCompileWrong a b
    N4 64 a b c   -> valuN PragmaExpectsUnambiguousConstructorOrFunction a b c
    N4 65 a b c   -> valuN PragmaExpectsUnambiguousProjectionOrFunction a b c
    N3 66 a b     -> valuN PragmaExpectsDefinedSymbol a b
    N2 67 a       -> valuN UnfoldingWrongName a
    -- TODO: linearity
    -- [68, a, b, c]        -> valuN FixingQuantity a b c
    N4 69 a b c   -> valuN FixingRelevance a b c
    N2 70 a       -> valuN UnusedVariablesInDisplayForm a
    N3 71 a b     -> valuN TooManyPolarities a b
    N4 72 a b c   -> valuN FixingCohesion a b c
    N4 73 a b c   -> valuN FixingPolarity a b c
    N1 74         -> valuN RewritesNothing
    N3 75 a b     -> valuN UnusedImports a b
    _ -> malformed

instance EmbPrj UselessPublicReason

instance EmbPrj RewriteSource where
  icod_ = \case
    LocalRewrite    -> icodeN 0 LocalRewrite
    GlobalRewrite a -> icodeN 1 GlobalRewrite a

  value = vcase $ \case
    N1 0   -> valuN LocalRewrite
    N2 1 a -> valuN GlobalRewrite a
    _      -> malformed

instance EmbPrj IllegalRewriteRuleReason where
  icod_ = \case
    LHSNotDefinitionOrConstructor               -> icodeN 0 LHSNotDefinitionOrConstructor
    VariablesNotBoundByLHS a                    -> icodeN 1 VariablesNotBoundByLHS a
    VariablesBoundMoreThanOnce a                -> icodeN 2 VariablesBoundMoreThanOnce a
    LHSReduces a b                              -> icodeN 3 LHSReduces a b
    VariablesBoundInSingleton a                 -> icodeN 4 VariablesBoundInSingleton a
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
    LetBoundLocalRewrite                        -> icodeN 16 LetBoundLocalRewrite
    LambdaBoundLocalRewrite                     -> icodeN 17 LambdaBoundLocalRewrite
    LocalRewriteOutsideTelescope                -> icodeN 18 LocalRewriteOutsideTelescope

  value = vcase $ \case
    N1 0     -> valuN LHSNotDefinitionOrConstructor
    N2 1 a   -> valuN VariablesNotBoundByLHS a
    N2 2 a   -> valuN VariablesBoundMoreThanOnce a
    N3 3 a b -> valuN LHSReduces a b
    N2 4 a   -> valuN VariablesBoundInSingleton a
    N2 5 a   -> valuN HeadSymbolIsProjectionLikeFunction a
    N2 6 a   -> valuN HeadSymbolIsTypeConstructor a
    N2 7 a   -> valuN HeadSymbolContainsMetas a
    N3 8 a b -> valuN ConstructorParametersNotGeneral a b
    N2 9 a   -> valuN ContainsUnsolvedMetaVariables a
    N2 10 a  -> valuN BlockedOnProblems a
    N2 11 a  -> valuN RequiresDefinitions a
    N1 12    -> valuN DoesNotTargetRewriteRelation
    N1 13    -> valuN BeforeFunctionDefinition
    N2 14 a  -> valuN BeforeMutualFunctionDefinition a
    N1 15    -> valuN DuplicateRewriteRule
    N1 16    -> valuN LetBoundLocalRewrite
    N1 17    -> valuN LambdaBoundLocalRewrite
    N1 18    -> valuN LocalRewriteOutsideTelescope
    _        -> malformed

instance EmbPrj OptionWarning where
  icod_ = \case
    OptionRenamed a b -> icodeN 0 OptionRenamed a b
    WarningProblem a  -> icodeN 1 WarningProblem a

  value = vcase $ \case
    N3 0 a b -> valuN OptionRenamed a b
    N2 1 a   -> valuN WarningProblem a
    _        -> malformed

instance EmbPrj WarningModeError where
  icod_ = \case
    Unknown a   -> icodeN 0 Unknown a
    NoNoError a -> icodeN 1 NoNoError a
    NoUnusedImportsAll -> icodeN 2 NoUnusedImportsAll

  value = vcase $ \case
    N2 0 a -> valuN Unknown a
    N2 1 a -> valuN NoNoError a
    N1 2   -> valuN NoUnusedImportsAll
    _      -> malformed

instance EmbPrj OpenBracket where
  icod_ = \case
    OpenIdiomBracket a b -> icodeN 0 OpenIdiomBracket a b
    OpenDoubleBrace  a b -> icodeN 1 OpenDoubleBrace a b

  value = vcase \case
    N3 0 a b -> valuN OpenIdiomBracket a b
    N3 1 a b -> valuN OpenDoubleBrace a b
    _        -> malformed

instance EmbPrj ParseWarning where
  icod_ = \case
    OverlappingTokensWarning a -> icodeN 0 OverlappingTokensWarning a
    UnsupportedAttribute a b   -> icodeN 1 UnsupportedAttribute a b
    MultipleAttributes a b     -> icodeN 2 MultipleAttributes a b
    UnknownAttribute a b       -> icodeN 3 UnknownAttribute a b
    UnknownPolarity a b        -> icodeN 4 UnknownPolarity a b
    MisplacedAttributes a b    -> icodeN 5 MisplacedAttributes a b
    MismatchedBrackets a b     -> icodeN 6 MismatchedBrackets a b

  value = vcase $ \case
    N2 0 a   -> valuN OverlappingTokensWarning a
    N3 1 a b -> valuN UnsupportedAttribute a b
    N3 2 a b -> valuN MultipleAttributes a b
    N3 3 a b -> valuN UnknownAttribute a b
    N3 4 a b -> valuN UnknownPolarity a b
    N3 5 a b -> valuN MisplacedAttributes a b
    N3 6 a b -> valuN MismatchedBrackets a b
    _        -> malformed

instance EmbPrj RecordFieldWarning where
  icod_ = \case
    W.DuplicateFields a   -> icodeN 0 W.DuplicateFields a
    W.TooManyFields a b c -> icodeN 1 W.TooManyFields a b c

  value = vcase $ \case
    N2 0 a     -> valuN W.DuplicateFields a
    N4 1 a b c -> valuN W.TooManyFields a b c
    _          -> malformed

instance EmbPrj DeclarationWarning where
  icod_ (DeclarationWarning a b) = icodeN' DeclarationWarning a b
  value = vcase $ \case
    N2 a b -> valuN DeclarationWarning a b
    _      -> malformed

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
    OpenImportAbstract r kwr a        -> icodeN 26 OpenImportAbstract r kwr a
    OpenImportPrivate r kwr kwr' a    -> icodeN 27 OpenImportPrivate r kwr kwr' a
    EmptyConstructor a                -> icodeN 28 EmptyConstructor a
    DivergentModalityInClause ai1 ai2 -> icodeN 29 DivergentModalityInClause ai1 ai2
    InvalidTacticAttribute r          -> icodeN 30 InvalidTacticAttribute r
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
    UselessImport r                   -> icodeN 36 UselessImport r
    InvalidDataOrRecDefParameter r a b c -> icodeN 37 InvalidDataOrRecDefParameter r a b c

  value = vcase $ \case
    N2 0  a            -> valuN UnknownNamesInFixityDecl a
    N2 1  a            -> valuN UnknownNamesInPolarityPragmas a
    N2 2  a            -> valuN PolarityPragmasButNotPostulates a
    N2 3  a            -> valuN UselessPrivate a
    N2 4  a            -> valuN UselessAbstract a
    N2 5  a            -> valuN UselessInstance a
    N2 6  a            -> valuN EmptyMutual a
    N2 7  a            -> valuN EmptyAbstract a
    N2 8  a            -> valuN EmptyPrivate a
    N2 9  a            -> valuN EmptyInstance a
    N2 10 a            -> valuN EmptyMacro a
    N2 11 a            -> valuN EmptyPostulate a
    N2 12 a            -> valuN InvalidTerminationCheckPragma a
    N2 13 a            -> valuN InvalidNoPositivityCheckPragma a
    N2 14 a            -> valuN InvalidCatchallPragma a
    N2 15 a            -> valuN InvalidNoUniverseCheckPragma a
    N2 16 a            -> valuN UnknownFixityInMixfixDecl a
    N2 17 a            -> valuN MissingDefinitions a
    N3 18 r a          -> valuN NotAllowedInMutual r a
    N2 19 r            -> valuN PragmaNoTerminationCheck r
    N2 20 a            -> valuN EmptyGeneralize a
    N2 21 a            -> valuN PragmaCompiled a
    N2 22 a            -> valuN EmptyPrimitive a
    N2 23 r            -> valuN EmptyField r
    N2 24 nrs          -> valuN ShadowingInTelescope nrs
    N2 25 r            -> valuN InvalidCoverageCheckPragma r
    N4 26 r kwr a      -> valuN OpenImportAbstract r kwr a
    N5 27 r kwr kwr' a -> valuN OpenImportPrivate r kwr kwr' a
    N2 28 r            -> valuN EmptyConstructor r
    N3 29 a b          -> valuN DivergentModalityInClause a b
    N2 30 r            -> valuN InvalidTacticAttribute r
    N2 31 r            -> valuN InvalidConstructorBlock r
    N2 32 r            -> valuN MissingDataDeclaration r
    N2 33 r            -> valuN HiddenGeneralize r
    N2 34 r            -> valuN UselessMacro r
    N2 35 r            -> valuN EmptyPolarityPragma r
    N2 36 r            -> valuN UselessImport r
    N5 37 r a b c      -> valuN InvalidDataOrRecDefParameter r a b c
    _ -> malformed

instance EmbPrj OpenOrImport

instance EmbPrj LibWarning where
  icod_ = \case
    LibWarning a b -> icodeN 0 LibWarning a b

  value = vcase $ \case
    N3 0 a b   -> valuN LibWarning a b
    _ -> malformed

instance EmbPrj LibWarning' where
  icod_ = \case
    UnknownField     a   -> icodeN 0 UnknownField a

  value = vcase $ \case
    N2 0 a    -> valuN UnknownField a
    _ -> malformed

instance EmbPrj ExecutablesFile where
  icod_ = \case
    ExecutablesFile a b -> icodeN 0 ExecutablesFile a b

  value = vcase $ \case
    N3 0 a b -> valuN ExecutablesFile a b
    _ -> malformed

instance EmbPrj LibPositionInfo where
  icod_ = \case
    LibPositionInfo a b c -> icodeN 0 LibPositionInfo a b c

  value = vcase $ \case
    N4 0 a b c -> valuN LibPositionInfo a b c
    _ -> malformed

-- Andreas, 2025-08-01, PR #8040:
-- We serialize Doc as DocTree, fixing the layout,
-- but preserving the annotations.
instance EmbPrj Doc where
  icod_ d = icodeN' (undefined :: DocTree -> Doc) (DocTree.renderToTree d)
  value = valueN DocTree.prettyDocTree

instance EmbPrj InfectiveCoinfective where
  icod_ Infective   = icodeN' Infective
  icod_ Coinfective = icodeN 0 Coinfective

  value = vcase valu where
    valu N0     = valuN Infective
    valu (N1 0) = valuN Coinfective
    valu _      = malformed

instance EmbPrj PragmaOptions where
  icod_    (PragmaOptions a b c d e f g h i j k l m n o p q r s t u v w x y z aa bb cc dd ee ff gg hh ii jj kk ll mm nn oo pp qq rr ss tt uu vv ww xx yy zz aaa bbb ccc ddd eee fff ggg hhh iii jjj kkk lll mmm nnn ooo ppp qqq rrr sss ttt uuu) =
    icodeN' PragmaOptions a b c d e f g h i j k l m n o p q r s t u v w x y z aa bb cc dd ee ff gg hh ii jj kk ll mm nn oo pp qq rr ss tt uu vv ww xx yy zz aaa bbb ccc ddd eee fff ggg hhh iii jjj kkk lll mmm nnn ooo ppp qqq rrr sss ttt uuu

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
    valu N0     = valuN LocalConfluenceCheck
    valu (N1 0) = valuN GlobalConfluenceCheck
    valu _      = malformed

instance EmbPrj WarningMode where
  icod_ (WarningMode a b) = icodeN' WarningMode a b

  value = valueN WarningMode

-- Andreas, 2024-08-18
-- Removed manual implementation of EmbPrj for this Enum type.
instance EmbPrj WarningName

instance EmbPrj CutOff where
  icod_ = \case
    DontCutOff -> icodeN' DontCutOff
    CutOff a   -> icodeN 0 CutOff a

  value = vcase valu where
    valu N0       = valuN DontCutOff
    valu (N2 0 a) = valuN CutOff a
    valu _        = malformed
