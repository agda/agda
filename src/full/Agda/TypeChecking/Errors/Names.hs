-- | Convert errors to their names.

module Agda.TypeChecking.Errors.Names where

import Agda.Syntax.Concrete.Definitions.Errors as N (DeclarationException'(..))
import Agda.TypeChecking.Monad.Base            as MB
import Agda.Interaction.Options.Errors

-- | Print the name of a 'TypeError'.
--
typeErrorString :: TypeError -> String
typeErrorString = errorNameString . typeErrorName

-- | Compute the name of a 'TypeError'.
--
typeErrorName :: TypeError -> ErrorName
typeErrorName = \case
  -- Error groups (alphabetically) with named sub errors
  ExecError                err -> ExecError_             $ execErrorName                  err
  GHCBackendError          err -> GHCBackendError_       $ ghcBackendErrorName            err
  JSBackendError           err -> JSBackendError_        $ jsBackendErrorName             err
  ImpossibleConstructor _  err -> ImpossibleConstructor_ $ impossibleConstructorErrorName err
  InteractionError         err -> InteractionError_      $ interactionErrorName           err
  NicifierError            err -> NicifierError_         $ declarationExceptionName       err
  SplitError               err -> SplitError_            $ splitErrorName                 err
  UnquoteFailed            err -> UnquoteError_          $ unquoteErrorName               err
  -- Parametrized errors
  CannotQuote             what -> CannotQuote_           $ unquotableName                 what
  MissingTypeSignature    what -> MissingTypeSignature_  $ missingTypeSignatureInfoName   what
  InvalidPun            kind _ -> InvalidPun_              kind
  CannotQuoteTerm         what -> CannotQuoteTerm_         what
  NotAllowedInDotPatterns what -> NotAllowedInDotPatterns_ what
  NotAValidLetBinding     what -> NotAValidLetBinding_     what
  NotAValidLetExpression  what -> NotAValidLetExpression_  what
  PatternSynonymArgumentShadows what _ _ -> PatternSynonymArgumentShadows_ what
  -- Wrappers
  OperatorInformation _    err -> typeErrorName err
  -- Generic errors (alphabetically)
  CompilationError          {} -> CompilationError_
  CustomBackendError        {} -> CustomBackendError_
  GenericError              {} -> GenericError_
  GenericDocError           {} -> GenericDocError_
  InternalError             {} -> InternalError_
  LibraryError              {} -> LibraryError_
  NonFatalErrors            {} -> NonFatalErrors_
  NotImplemented            {} -> NotImplemented_
  NotSupported              {} -> NotSupported_
  OptionError               {} -> OptionError_
  SyntaxError               {} -> SyntaxError_
  -- Other errors (alphabetically)
  AbsentRHSRequiresAbsurdPattern                             {} -> AbsentRHSRequiresAbsurdPattern_
  AbstractConstructorNotInScope                              {} -> AbstractConstructorNotInScope_
  MB.AmbiguousConstructor                                    {} -> AmbiguousConstructor_
  AmbiguousField                                             {} -> AmbiguousField_
  AmbiguousModule                                            {} -> AmbiguousModule_
  AmbiguousName                                              {} -> AmbiguousName_
  AmbiguousOverloadedProjection                              {} -> AmbiguousOverloadedProjection_
  AmbiguousParseForApplication                               {} -> AmbiguousParseForApplication_
  AmbiguousParseForLHS                                       {} -> AmbiguousParseForLHS_
  AmbiguousProjection                                        {} -> AmbiguousProjection_
  AmbiguousTopLevelModuleName                                {} -> AmbiguousTopLevelModuleName_
  AsPatternInPatternSynonym                                  {} -> AsPatternInPatternSynonym_
  AttributeKindNotEnabled                                    {} -> AttributeKindNotEnabled_
  BackendDoesNotSupportOnlyScopeChecking                     {} -> BackendDoesNotSupportOnlyScopeChecking_
  BadArgumentsToPatternSynonym                               {} -> BadArgumentsToPatternSynonym_
  BuiltinInParameterisedModule                               {} -> BuiltinInParameterisedModule_
  BuiltinMustBeConstructor                                   {} -> BuiltinMustBeConstructor_
  CannotEliminateWithPattern                                 {} -> CannotEliminateWithPattern_
  CannotEliminateWithProjection                              {} -> CannotEliminateWithProjection_
  CannotGenerateHCompClause                                  {} -> CannotGenerateHCompClause_
  CannotGenerateTransportClause                              {} -> CannotGenerateTransportClause_
  CannotResolveAmbiguousPatternSynonym                       {} -> CannotResolveAmbiguousPatternSynonym_
  CannotRewriteByNonEquation                                 {} -> CannotRewriteByNonEquation_
  CannotSolveSizeConstraints                                 {} -> CannotSolveSizeConstraints_
  CantResolveOverloadedConstructorsTargetingSameDatatype     {} -> CantResolveOverloadedConstructorsTargetingSameDatatype_
  ClashingDefinition                                         {} -> ClashingDefinition_
  ClashingModule                                             {} -> ClashingModule_
  ComatchingDisabledForRecord                                {} -> ComatchingDisabledForRecord_
  ConstructorDoesNotTargetGivenType                          {} -> ConstructorDoesNotTargetGivenType_
  ConstructorNameOfNonRecord                                 {} -> ConstructorNameOfNonRecord_
  ConstructorPatternInWrongDatatype                          {} -> ConstructorPatternInWrongDatatype_
  ContradictorySizeConstraint                                {} -> ContradictorySizeConstraint_
  CopatternHeadNotProjection                                 {} -> CopatternHeadNotProjection_
  CubicalCompilationNotSupported                             {} -> CubicalCompilationNotSupported_
  CubicalPrimitiveNotFullyApplied                            {} -> CubicalPrimitiveNotFullyApplied_
  CyclicModuleDependency                                     {} -> CyclicModuleDependency_
  DeBruijnIndexOutOfScope                                    {} -> DeBruijnIndexOutOfScope_
  DeclarationsAfterTopLevelModule                            {} -> DeclarationsAfterTopLevelModule_
  DefinitionInDifferentModule                                {} -> DefinitionInDifferentModule_
  DefinitionIsErased                                         {} -> DefinitionIsErased_
  DefinitionIsIrrelevant                                     {} -> DefinitionIsIrrelevant_
  DoNotationError                                            {} -> DoNotationError_
  DoesNotMentionTicks                                        {} -> DoesNotMentionTicks_
  DotPatternInPatternSynonym                                 {} -> DotPatternInPatternSynonym_
  DuplicateBuiltinBinding                                    {} -> DuplicateBuiltinBinding_
  DuplicateConstructors                                      {} -> DuplicateConstructors_
  DuplicateFields                                            {} -> DuplicateFields_
  DuplicateImports                                           {} -> DuplicateImports_
  DuplicateOverlapPragma                                     {} -> DuplicateOverlapPragma_
  DuplicatePrimitiveBinding                                  {} -> DuplicatePrimitiveBinding_
  EmptyTypeOfSizes                                           {} -> EmptyTypeOfSizes_
  ExpectedBindingForParameter                                {} -> ExpectedBindingForParameter_
  ExpectedIntervalLiteral                                    {} -> ExpectedIntervalLiteral_
  FieldOutsideRecord                                         {} -> FieldOutsideRecord_
  FileNotFound                                               {} -> FileNotFound_
  ForcedConstructorNotInstantiated                           {} -> ForcedConstructorNotInstantiated_
  FunctionTypeInSizeUniv                                     {} -> FunctionTypeInSizeUniv_
  GeneralizeCyclicDependency                                 {} -> GeneralizeCyclicDependency_
  GeneralizeNotSupportedHere                                 {} -> GeneralizeNotSupportedHere_
  GeneralizedVarInLetOpenedModule                            {} -> GeneralizedVarInLetOpenedModule_
  HidingMismatch                                             {} -> HidingMismatch_
  IdiomBracketError                                          {} -> IdiomBracketError_
  InvalidDottedExpression                                    {} -> InvalidDottedExpression_
  IllTypedPatternAfterWithAbstraction                        {} -> IllTypedPatternAfterWithAbstraction_
  IllegalDeclarationBeforeTopLevelModule                     {} -> IllegalDeclarationBeforeTopLevelModule_
  IllegalDeclarationInDataDefinition                         {} -> IllegalDeclarationInDataDefinition_
  IllegalHidingInPostfixProjection                           {} -> IllegalHidingInPostfixProjection_
  IllegalInstanceVariableInPatternSynonym                    {} -> IllegalInstanceVariableInPatternSynonym_
  IllegalLetInTelescope                                      {} -> IllegalLetInTelescope_
  IllegalPatternInTelescope                                  {} -> IllegalPatternInTelescope_
  IllformedProjectionPatternAbstract                         {} -> IllformedProjectionPatternAbstract_
  IllformedProjectionPatternConcrete                         {} -> IllformedProjectionPatternConcrete_
  IncorrectTypeForRewriteRelation                            {} -> IncorrectTypeForRewriteRelation_
  InstanceNoCandidate                                        {} -> InstanceNoCandidate_
  InstanceSearchDepthExhausted                               {} -> InstanceSearchDepthExhausted_
  InvalidFileName                                            {} -> InvalidFileName_
  InvalidModalTelescopeUse                                   {} -> InvalidModalTelescopeUse_
  InvalidPattern                                             {} -> InvalidPattern_
  InvalidProjectionParameter                                 {} -> InvalidProjectionParameter_
  InvalidTypeSort                                            {} -> InvalidTypeSort_
  LibTooFarDown                                              {} -> LibTooFarDown_
  LiteralTooBig                                              {} -> LiteralTooBig_
  MacroResultTypeMismatch                                    {} -> MacroResultTypeMismatch_
  MetaCannotDependOn                                         {} -> MetaCannotDependOn_
  MetaErasedSolution                                         {} -> MetaErasedSolution_
  MetaIrrelevantSolution                                     {} -> MetaIrrelevantSolution_
  MismatchedProjectionsError                                 {} -> MismatchedProjectionsError_
  ModuleArityMismatch                                        {} -> ModuleArityMismatch_
  ModuleDefinedInOtherFile                                   {} -> ModuleDefinedInOtherFile_
  ModuleNameDoesntMatchFileName                              {} -> ModuleNameDoesntMatchFileName_
  ModuleNameUnexpected                                       {} -> ModuleNameUnexpected_
  MultipleFixityDecls                                        {} -> MultipleFixityDecls_
  MultiplePolarityPragmas                                    {} -> MultiplePolarityPragmas_
  NamedWhereModuleInRefinedContext                           {} -> NamedWhereModuleInRefinedContext_
  NeedOptionAllowExec                                        {} -> NeedOptionAllowExec_
  NeedOptionCopatterns                                       {} -> NeedOptionCopatterns_
  NeedOptionCubical                                          {} -> NeedOptionCubical_
  NeedOptionPatternMatching                                  {} -> NeedOptionPatternMatching_
  NeedOptionProp                                             {} -> NeedOptionProp_
  NeedOptionRewriting                                        {} -> NeedOptionRewriting_
  NeedOptionSizedTypes                                       {} -> NeedOptionSizedTypes_
  NeedOptionTwoLevel                                         {} -> NeedOptionTwoLevel_
  NeedOptionUniversePolymorphism                             {} -> NeedOptionUniversePolymorphism_
  NegativeLiteralInPattern                                   {} -> NegativeLiteralInPattern_
  NoBindingForBuiltin                                        {} -> NoBindingForBuiltin_
  NoBindingForPrimitive                                      {} -> NoBindingForPrimitive_
  NoKnownRecordWithSuchFields                                {} -> NoKnownRecordWithSuchFields_
  NoParameterOfName                                          {} -> NoParameterOfName_
  NoParseForApplication                                      {} -> NoParseForApplication_
  NoParseForLHS                                              {} -> NoParseForLHS_
  NoSuchBuiltinName                                          {} -> NoSuchBuiltinName_
  NoSuchModule                                               {} -> NoSuchModule_
  NoSuchPrimitiveFunction                                    {} -> NoSuchPrimitiveFunction_
  NotAnExpression                                            {} -> NotAnExpression_
  NotInScope                                                 {} -> NotInScope_
  NotLeqSort                                                 {} -> NotLeqSort_
  NotValidBeforeField                                        {} -> NotValidBeforeField_
  OpenEverythingInRecordWhere                                {} -> OpenEverythingInRecordWhere_
  OverlappingProjects                                        {} -> OverlappingProjects_
  PatternInPathLambda                                        {} -> PatternInPathLambda_
  PatternInSystem                                            {} -> PatternInSystem_
  PrivateRecordField                                         {} -> PrivateRecordField_
  ProjectionIsIrrelevant                                     {} -> ProjectionIsIrrelevant_
  QualifiedLocalModule                                       {} -> QualifiedLocalModule_
  QuantityMismatch                                           {} -> QuantityMismatch_
  RecursiveRecordNeedsInductivity                            {} -> RecursiveRecordNeedsInductivity_
  ReferencesFutureVariables                                  {} -> ReferencesFutureVariables_
  RelevanceMismatch                                          {} -> RelevanceMismatch_
  RepeatedNamesInImportDirective                             {} -> RepeatedNamesInImportDirective_
  RepeatedVariablesInPattern                                 {} -> RepeatedVariablesInPattern_
  ShadowedModule                                             {} -> ShadowedModule_
  ShouldBeASort                                              {} -> ShouldBeASort_
  ShouldBeEmpty                                              {} -> ShouldBeEmpty_
  ShouldBePath                                               {} -> ShouldBePath_
  ShouldBePi                                                 {} -> ShouldBePi_
  ShouldBeRecordPattern                                      {} -> ShouldBeRecordPattern_
  ShouldBeRecordType                                         {} -> ShouldBeRecordType_
  ShouldEndInApplicationOfTheDatatype                        {} -> ShouldEndInApplicationOfTheDatatype_
  SolvedButOpenHoles                                         {} -> SolvedButOpenHoles_
  SortCannotDependOnItsIndex                                 {} -> SortCannotDependOnItsIndex_
  SortDoesNotAdmitDataDefinitions                            {} -> SortDoesNotAdmitDataDefinitions_
  SortOfSplitVarError                                        {} -> SortOfSplitVarError_
  SplitInProp                                                {} -> SplitInProp_
  SplitOnAbstract                                            {} -> SplitOnAbstract_
  SplitOnCoinductive                                         {} -> SplitOnCoinductive_
  SplitOnIrrelevant                                          {} -> SplitOnIrrelevant_
  SplitOnNonEtaRecord                                        {} -> SplitOnNonEtaRecord_
  SplitOnNonVariable                                         {} -> SplitOnNonVariable_
  SplitOnPartial                                             {} -> SplitOnPartial_
  SplitOnUnchecked                                           {} -> SplitOnUnchecked_
  SplitOnUnusableCohesion                                    {} -> SplitOnUnusableCohesion_
  SplitOnUnusablePolarity                                    {} -> SplitOnUnusablePolarity_
  TacticAttributeNotAllowed                                  {} -> TacticAttributeNotAllowed_
  TooFewArgumentsToPatternSynonym                            {} -> TooFewArgumentsToPatternSynonym_
  TooFewPatternsInWithClause                                 {} -> TooFewPatternsInWithClause_
  TooManyFields                                              {} -> TooManyFields_
  TooManyPatternsInWithClause                                {} -> TooManyPatternsInWithClause_
  TooManyPolarities                                          {} -> TooManyPolarities_
  TriedToCopyConstrainedPrim                                 {} -> TriedToCopyConstrainedPrim_
  InvalidInstanceHeadType                                    {} -> InvalidInstanceHeadType_
  UnboundVariablesInPatternSynonym                           {} -> UnboundVariablesInPatternSynonym_
  UnequalCohesion                                            {} -> UnequalCohesion_
  UnequalFiniteness                                          {} -> UnequalFiniteness_
  UnequalHiding                                              {} -> UnequalHiding_
  UnequalLevel                                               {} -> UnequalLevel_
  UnequalQuantity                                            {} -> UnequalQuantity_
  UnequalRelevance                                           {} -> UnequalRelevance_
  UnequalPolarity                                            {} -> UnequalPolarity_
  UnequalSorts                                               {} -> UnequalSorts_
  UnequalTerms                                               {} -> UnequalTerms_
  UnexpectedModalityAnnotationInParameter                    {} -> UnexpectedModalityAnnotationInParameter_
  UnexpectedParameter                                        {} -> UnexpectedParameter_
  UnexpectedTypeSignatureForParameter                        {} -> UnexpectedTypeSignatureForParameter_
  UnexpectedWithPatterns                                     {} -> UnexpectedWithPatterns_
  UnknownBackend                                             {} -> UnknownBackend_
  UnusableAtModality                                         {} -> UnusableAtModality_
  UnusedVariableInPatternSynonym                             {} -> UnusedVariableInPatternSynonym_
  VariableIsErased                                           {} -> VariableIsErased_
  VariableIsIrrelevant                                       {} -> VariableIsIrrelevant_
  VariableIsOfUnusableCohesion                               {} -> VariableIsOfUnusableCohesion_
  VariableIsOfUnusablePolarity                               {} -> VariableIsOfUnusablePolarity_
  WithClausePatternMismatch                                  {} -> WithClausePatternMismatch_
  WithOnFreeVariable                                         {} -> WithOnFreeVariable_
  WrongAnnotationInLambda                                    {} -> WrongAnnotationInLambda_
  WrongArgInfoForPrimitive                                   {} -> WrongArgInfoForPrimitive_
  WrongCohesionInLambda                                      {} -> WrongCohesionInLambda_
  WrongPolarityInLambda                                      {} -> WrongPolarityInLambda_
  WrongHidingInApplication                                   {} -> WrongHidingInApplication_
  WrongHidingInLHS                                           {} -> WrongHidingInLHS_
  WrongHidingInLambda                                        {} -> WrongHidingInLambda_
  WrongHidingInProjection                                    {} -> WrongHidingInProjection_
  WrongIrrelevanceInLambda                                   {} -> WrongIrrelevanceInLambda_
  WrongNamedArgument                                         {} -> WrongNamedArgument_
  WrongNumberOfConstructorArguments                          {} -> WrongNumberOfConstructorArguments_
  WrongQuantityInLambda                                      {} -> WrongQuantityInLambda_

declarationExceptionName :: DeclarationException' -> DeclarationException_
declarationExceptionName = \case
  N.AmbiguousConstructor           {} -> AmbiguousConstructorN_
  AmbiguousFunClauses              {} -> AmbiguousFunClauses_
  BadMacroDef                      {} -> BadMacroDef_
  DisallowedInterleavedMutual      {} -> DisallowedInterleavedMutual_
  DuplicateAnonDeclaration         {} -> DuplicateAnonDeclaration_
  DuplicateDefinition              {} -> DuplicateDefinition_
  InvalidMeasureMutual             {} -> InvalidMeasureMutual_
  MissingWithClauses               {} -> MissingWithClauses_
  MultipleEllipses                 {} -> MultipleEllipses_
  OpaqueInMutual                   {} -> OpaqueInMutual_
  UnfoldingOutsideOpaque           {} -> UnfoldingOutsideOpaque_
  UnquoteDefRequiresSignature      {} -> UnquoteDefRequiresSignature_
  WrongContentBlock                {} -> WrongContentBlock_
  WrongDefinition                  {} -> WrongDefinition_

execErrorName :: ExecError -> ExecError_
execErrorName = \case
  ExeNotTrusted    {} -> ExeNotTrusted_
  ExeNotFound      {} -> ExeNotFound_
  ExeNotExecutable {} -> ExeNotExecutable_

ghcBackendErrorName :: GHCBackendError -> GHCBackendError_
ghcBackendErrorName = \case
  ConstructorCountMismatch{} -> ConstructorCountMismatch_
  NotAHaskellType _ err      -> NotAHaskellType_ $ notAHaskellTypeErrorName err
  WrongTypeOfMain{}          -> WrongTypeOfMain_

jsBackendErrorName :: JSBackendError -> JSBackendError_
jsBackendErrorName = \case
  BadCompilePragma -> BadCompilePragma_

impossibleConstructorErrorName :: NegativeUnification -> NegativeUnification_
impossibleConstructorErrorName = \case
  UnifyConflict {} -> UnifyConflict_
  UnifyCycle    {} -> UnifyCycle_

interactionErrorName :: InteractionError -> InteractionError_
interactionErrorName = \case
  CaseSplitError{}              -> CaseSplitError_
  CannotRefine{}                -> CannotRefine_
  ExpectedIdentifier{}          -> ExpectedIdentifier_
  ExpectedApplication{}         -> ExpectedApplication_
  NoActionForInteractionPoint{} -> NoActionForInteractionPoint_
  NoSuchInteractionPoint{}      -> NoSuchInteractionPoint_
  UnexpectedWhere{}             -> UnexpectedWhere_

missingTypeSignatureInfoName :: MissingTypeSignatureInfo -> DataRecOrFun_
missingTypeSignatureInfoName = \case
  MissingDataSignature      {} -> DataName_
  MissingRecordSignature    {} -> RecName_
  MissingFunctionSignature  {} -> FunName_

notAHaskellTypeErrorName :: WhyNotAHaskellType -> NotAHaskellType_
notAHaskellTypeErrorName = \case
  BadDontCare               {} -> BadDontCare_
  BadLambda                 {} -> BadLambda_
  BadMeta                   {} -> BadMeta_
  NoPragmaFor               {} -> NoPragmaFor_
  NotCompiled               {} -> NotCompiled_
  WrongPragmaFor            {} -> WrongPragmaFor_

splitErrorName :: SplitError -> SplitError_
splitErrorName = \case
  ErasedDatatype reason _      -> ErasedDatatype_ reason
  GenericSplitError         {} -> GenericSplitError_
  -- Specific errors
  BlockedType               {} -> BlockedType_
  CannotCreateMissingClause {} -> CannotCreateMissingClause_
  CoinductiveDatatype       {} -> CoinductiveDatatype_
  CosplitCatchall           {} -> CosplitCatchall_
  CosplitNoRecordType       {} -> CosplitNoRecordType_
  CosplitNoTarget           {} -> CosplitNoTarget_
  NotADatatype              {} -> NotADatatype_
  UnificationStuck          {} -> UnificationStuck_

unquotableName :: CannotQuote -> CannotQuote_
unquotableName = \case
  CannotQuoteAmbiguous         {} -> CannotQuoteAmbiguous_
  CannotQuoteExpression        {} -> CannotQuoteExpression_
  CannotQuoteHidden            {} -> CannotQuoteHidden_
  CannotQuoteNothing           {} -> CannotQuoteNothing_
  CannotQuotePattern           {} -> CannotQuotePattern_

unquoteErrorName :: UnquoteError -> UnquoteError_
unquoteErrorName = \case
  CannotDeclareHiddenFunction {} -> CannotDeclareHiddenFunction_
  ConInsteadOfDef             {} -> ConInsteadOfDef_
  DefInsteadOfCon             {} -> DefInsteadOfCon_
  MissingDeclaration          {} -> MissingDeclaration_
  MissingDefinition           {} -> MissingDefinition_
  NakedUnquote                {} -> NakedUnquote_
  NonCanonical                {} -> NonCanonical_
  BlockedOnMeta               {} -> BlockedOnMeta_
  PatLamWithoutClauses        {} -> PatLamWithoutClauses_
  StaleMeta                   {} -> StaleMeta_

-- -- * Printing names of errors

-- -- The following might not be used yet:

-- ghcBackendErrorString :: GHCBackendError -> String
-- ghcBackendErrorString = ghcBackendErrorNameString . ghcBackendErrorName

-- interactionErrorString :: InteractionError -> String
-- interactionErrorString = interactionErrorNameString . interactionErrorName

-- splitErrorString :: SplitError -> String
-- splitErrorString = splitErrorNameString . splitErrorName

-- unquoteErrorString :: UnquoteError -> String
-- unquoteErrorString = unquoteErrorNameString . unquoteErrorName
