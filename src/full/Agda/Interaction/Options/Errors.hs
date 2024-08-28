-- | Provide names for the errors Agda throws.

module Agda.Interaction.Options.Errors where

import Control.DeepSeq        ( NFData )
import Data.List              ( sort )
import Generic.Data           ( FiniteEnumeration(..) )
import GHC.Generics           ( Generic )

import Agda.Utils.Function    ( applyWhenJust )
import Agda.Utils.List        ( initWithDefault )
import Agda.Utils.Impossible  ( __IMPOSSIBLE__ )

-- | The reason for an 'ErasedDatatype' error.

data ErasedDatatypeReason
  = SeveralConstructors
    -- ^ There are several constructors.
  | NoErasedMatches
    -- ^ The flag @--erased-matches@ is not used.
  | NoK
    -- ^ The K rule is not activated.
  deriving (Show, Generic, Enum, Bounded)

-- | Things not allowed in dot patterns.

data NotAllowedInDotPatterns
  = LetExpressions
  | PatternLambdas
  deriving (Show, Generic, Enum, Bounded)

-- | Reasons for error 'NotAValidLetBinding'.

data NotAValidLetBinding
  = AbstractNotAllowed
  | MacrosNotAllowed
  | MissingRHS
  | NotAValidLetPattern
  | WhereClausesNotAllowed
  -- These cannot be triggered:
  -- -- | CopatternsNotAllowed
  -- -- | EllipsisNotAllowed
  -- -- | WithPatternsNotAllowed
  deriving (Show, Generic, Enum, Bounded)

-- | Reasons for error 'NotAValidLetExpression'.

data NotAValidLetExpression
  = MissingBody
  deriving (Show, Generic, Enum, Bounded)

-- | Symbolic name of an Agda error.

data ErrorName
  -- Error groups (alphabetically) with named sub errors
  = GHCBackendError_       GHCBackendError_
  | ImpossibleConstructor_ NegativeUnification_
  | InteractionError_      InteractionError_
  | NicifierError_         DeclarationException_
  | SplitError_            SplitError_
  | UnquoteError_          UnquoteError_
  -- Generic errors (alphabetically)
  | CompilationError_
  | CustomBackendError_
  | GenericError_
  | GenericDocError_
  | InternalError_
  | LibraryError_
  | NonFatalErrors_
  | NotImplemented_
  | NotSupported_
  | OptionError_
  | SyntaxError_
  -- Other errors (alphabetically)
  | AbsentRHSRequiresAbsurdPattern_
  | AbstractConstructorNotInScope_
  | AmbiguousConstructor_
  | AmbiguousField_
  | AmbiguousModule_
  | AmbiguousName_
  | AmbiguousOverloadedProjection_
  | AmbiguousParseForApplication_
  | AmbiguousParseForLHS_
  | AmbiguousProjection_
  | AmbiguousTopLevelModuleName_
  | AsPatternInPatternSynonym_
  | AttributeKindNotEnabled_
  | BadArgumentsToPatternSynonym_
  | BuiltinInParameterisedModule_
  | BuiltinMustBeConstructor_
  | CannotEliminateWithPattern_
  | CannotEliminateWithProjection_
  | CannotGenerateHCompClause_
  | CannotGenerateTransportClause_
  | CannotResolveAmbiguousPatternSynonym_
  | CannotRewriteByNonEquation_
  | CannotSolveSizeConstraints_
  | CantResolveOverloadedConstructorsTargetingSameDatatype_
  | ClashingDefinition_
  | ClashingModule_
  | ComatchingDisabledForRecord_
  | ConstructorDoesNotTargetGivenType_
  | ConstructorPatternInWrongDatatype_
  | ContradictorySizeConstraint_
  | CubicalCompilationNotSupported_
  | CubicalPrimitiveNotFullyApplied_
  | CyclicModuleDependency_
  | DeBruijnIndexOutOfScope_
  | DefinitionInDifferentModule_
  | DefinitionIsErased_
  | DefinitionIsIrrelevant_
  | DoesNotMentionTicks_
  | DotPatternInPatternSynonym_
  | DuplicateBuiltinBinding_
  | DuplicateConstructors_
  | DuplicateFields_
  | DuplicateImports_
  | DuplicateOverlapPragma_
  | DuplicatePrimitiveBinding_
  | EmptyTypeOfSizes_
  | ExpectedBindingForParameter_
  | ExpectedIntervalLiteral_
  | FieldOutsideRecord_
  | FileNotFound_
  | ForcedConstructorNotInstantiated_
  | FunctionTypeInSizeUniv_
  | GeneralizeCyclicDependency_
  | GeneralizeNotSupportedHere_
  | GeneralizedVarInLetOpenedModule_
  | HidingMismatch_
  | IllTypedPatternAfterWithAbstraction_
  | IllegalDeclarationInDataDefinition_
  | IllegalHidingInPostfixProjection_
  | IllegalInstanceVariableInPatternSynonym_
  | IllegalLetInTelescope_
  | IllegalPatternInTelescope_
  | IllformedProjectionPatternAbstract_
  | IllformedProjectionPatternConcrete_
  | IncorrectTypeForRewriteRelation_
  | InstanceNoCandidate_
  | InstanceSearchDepthExhausted_
  | InvalidFileName_
  | InvalidModalTelescopeUse_
  | InvalidPattern_
  | InvalidProjectionParameter_
  | InvalidTypeSort_
  | LibTooFarDown_
  | LiteralTooBig_
  | MacroResultTypeMismatch_
  | MetaCannotDependOn_
  | MetaErasedSolution_
  | MetaIrrelevantSolution_
  | MetaOccursInItself_
  | MismatchedProjectionsError_
  | ModuleArityMismatch_
  | ModuleDefinedInOtherFile_
  | ModuleNameDoesntMatchFileName_
  | ModuleNameUnexpected_
  | MultipleFixityDecls_
  | MultiplePolarityPragmas_
  | NamedWhereModuleInRefinedContext_
  | NeedOptionAllowExec_
  | NeedOptionCopatterns_
  | NeedOptionCubical_
  | NeedOptionPatternMatching_
  | NeedOptionProp_
  | NeedOptionRewriting_
  | NeedOptionSizedTypes_
  | NeedOptionTwoLevel_
  | NeedOptionUniversePolymorphism_
  | NegativeLiteralInPattern_
  | NoBindingForBuiltin_
  | NoBindingForPrimitive_
  | NoKnownRecordWithSuchFields_
  | NoParameterOfName_
  | NoParseForApplication_
  | NoParseForLHS_
  | NoSuchBuiltinName_
  | NoSuchModule_
  | NoSuchPrimitiveFunction_
  | NotAValidLetBinding_ (Maybe NotAValidLetBinding)
  | NotAValidLetExpression_ NotAValidLetExpression
  | NotAllowedInDotPatterns_ NotAllowedInDotPatterns
  | NotAnExpression_
  | NotInScope_
  | NotLeqSort_
  | NotValidBeforeField_
  | NothingAppliedToHiddenArg_
  | NothingAppliedToInstanceArg_
  | OverlappingProjects_
  | PatternInPathLambda_
  | PatternInSystem_
  | PatternSynonymArgumentShadowsConstructorOrPatternSynonym_
  | ProjectionIsIrrelevant_
  | QuantityMismatch_
  | RecursiveRecordNeedsInductivity_
  | ReferencesFutureVariables_
  | RelevanceMismatch_
  | RepeatedVariablesInPattern_
  | ShadowedModule_
  | ShouldBeASort_
  | ShouldBeEmpty_
  | ShouldBePath_
  | ShouldBePi_
  | ShouldBeRecordPattern_
  | ShouldBeRecordType_
  | ShouldEndInApplicationOfTheDatatype_
  | SolvedButOpenHoles_
  | SortCannotDependOnItsIndex_
  | SortDoesNotAdmitDataDefinitions_
  | SortOfSplitVarError_
  | SplitInProp_
  | SplitOnAbstract_
  | SplitOnCoinductive_
  | SplitOnIrrelevant_
  | SplitOnNonEtaRecord_
  | SplitOnNonVariable_
  | SplitOnPartial_
  | SplitOnUnchecked_
  | SplitOnUnusableCohesion_
  | TacticAttributeNotAllowed_
  | TooFewArgumentsToPatternSynonym_
  | TooFewPatternsInWithClause_
  | TooManyFields_
  | TooManyPatternsInWithClause_
  | TooManyPolarities_
  | TriedToCopyConstrainedPrim_
  | UnboundVariablesInPatternSynonym_
  | UnequalCohesion_
  | UnequalFiniteness_
  | UnequalHiding_
  | UnequalLevel_
  | UnequalQuantity_
  | UnequalRelevance_
  | UnequalSorts_
  | UnequalTerms_
  | UnexpectedModalityAnnotationInParameter_
  | UnexpectedParameter_
  | UnexpectedTypeSignatureForParameter_
  | UnexpectedWithPatterns_
  | UnusableAtModality_
  | UnusedVariableInPatternSynonym_
  | VariableIsErased_
  | VariableIsIrrelevant_
  | VariableIsOfUnusableCohesion_
  | WithClausePatternMismatch_
  | WithOnFreeVariable_
  | WrongAnnotationInLambda_
  | WrongArgInfoForPrimitive_
  | WrongCohesionInLambda_
  | WrongHidingInApplication_
  | WrongHidingInLHS_
  | WrongHidingInLambda_
  | WrongHidingInProjection_
  | WrongIrrelevanceInLambda_
  | WrongNamedArgument_
  | WrongNumberOfConstructorArguments_
  | WrongQuantityInLambda_
  deriving (Show, Generic)
  deriving (Enum, Bounded) via (FiniteEnumeration ErrorName)

-- | Nicifier errors.
--
data DeclarationException_
  = AmbiguousConstructorN_
  | AmbiguousFunClauses_
  | BadMacroDef_
  | DeclarationPanic_
  | DisallowedInterleavedMutual_
  | DuplicateAnonDeclaration_
  | DuplicateDefinition_
  | InvalidMeasureMutual_
  | InvalidName_
  | MissingWithClauses_
  | MultipleEllipses_
  | OpaqueInMutual_
  | UnfoldingOutsideOpaque_
  | UnquoteDefRequiresSignature_
  | WrongContentBlock_
  | WrongDefinition_
  deriving (Show, Generic)
  deriving (Enum, Bounded) via (FiniteEnumeration DeclarationException_)

data GHCBackendError_
  = ConstructorCountMismatch_
  | NotAHaskellType_ NotAHaskellType_
  | WrongTypeOfMain_
  deriving (Show, Generic)
  deriving (Enum, Bounded) via (FiniteEnumeration GHCBackendError_)

data InteractionError_
  = CannotRefine_
  | CaseSplitError_
  | ExpectedIdentifier_
  | ExpectedApplication_
  | NoActionForInteractionPoint_
  | NoSuchInteractionPoint_
  | UnexpectedWhere_
  deriving (Show, Generic, Enum, Bounded)

data NegativeUnification_
  = UnifyConflict_
  | UnifyCycle_
  deriving (Show, Generic, Enum, Bounded)

data NotAHaskellType_
  = BadDontCare_
  | BadLambda_
  | BadMeta_
  | NoPragmaFor_
  | NotCompiled_
  | WrongPragmaFor_
  deriving (Show, Generic, Enum, Bounded)

data SplitError_
  = ErasedDatatype_ ErasedDatatypeReason
  | GenericSplitError_
  -- Specific errors
  | BlockedType_
  | CannotCreateMissingClause_
  | CoinductiveDatatype_
  | CosplitCatchall_
  | CosplitNoRecordType_
  | CosplitNoTarget_
  | NotADatatype_
  | UnificationStuck_
  deriving (Show, Generic)
  deriving (Enum, Bounded) via (FiniteEnumeration SplitError_)

data UnquoteError_
  = BadVisibility_
  | CannotDeclareHiddenFunction_
  | ConInsteadOfDef_
  | DefInsteadOfCon_
  | NonCanonical_
  | BlockedOnMeta_
  | PatLamWithoutClauses_
  | UnquotePanic_
  deriving (Show, Generic, Enum, Bounded)

-- * Printing error names
------------------------------------------------------------------------

defaultErrorNameString :: Show a => a -> String
defaultErrorNameString = initWithDefault __IMPOSSIBLE__ . show

erasedDatatypeReasonString :: ErasedDatatypeReason -> String
erasedDatatypeReasonString = show

errorNameString :: ErrorName -> String
errorNameString = \case
  GHCBackendError_        err -> "GHCBackend." ++ ghcBackendErrorNameString err
  ImpossibleConstructor_  err -> "ImpossibleConstructor." ++ negativeUnificationErrorNameString err
  InteractionError_       err -> "Interaction." ++ interactionErrorNameString err
  NicifierError_          err -> "Syntax." ++ declarationExceptionNameString err
  SplitError_             err -> "SplitError." ++ splitErrorNameString err
  UnquoteError_           err -> "Unquote." ++ unquoteErrorNameString err
  NotAllowedInDotPatterns_ err -> "NotAllowedInDotPatterns." ++ notAllowedInDotPatternsString err
  NotAValidLetBinding_    merr -> applyWhenJust merr (\ err hd -> hd ++ "." ++ notAValidLetBindingString err) "NotAValidLetBinding"
  NotAValidLetExpression_  err -> "NotAValidLetExpression." ++ notAValidLetExpressionString err
  err -> defaultErrorNameString err

declarationExceptionNameString :: DeclarationException_ -> String
declarationExceptionNameString = \case
  AmbiguousConstructorN_ -> "AmbiguousConstructor"
  err -> defaultErrorNameString err

ghcBackendErrorNameString :: GHCBackendError_ -> String
ghcBackendErrorNameString = \case
  NotAHaskellType_ err -> "NotAHaskellType." ++ notAHaskellTypeErrorNameString err
  err -> defaultErrorNameString err

interactionErrorNameString :: InteractionError_ -> String
interactionErrorNameString = defaultErrorNameString

negativeUnificationErrorNameString :: NegativeUnification_ -> String
negativeUnificationErrorNameString = defaultErrorNameString

notAHaskellTypeErrorNameString :: NotAHaskellType_ -> String
notAHaskellTypeErrorNameString = defaultErrorNameString

notAValidLetBindingString :: NotAValidLetBinding -> String
notAValidLetBindingString = show

notAValidLetExpressionString :: NotAValidLetExpression -> String
notAValidLetExpressionString = show

notAllowedInDotPatternsString :: NotAllowedInDotPatterns -> String
notAllowedInDotPatternsString = show

splitErrorNameString :: SplitError_ -> String
splitErrorNameString = \case
  ErasedDatatype_ err -> "ErasedDatatype." ++ erasedDatatypeReasonString err
  err -> defaultErrorNameString err

unquoteErrorNameString :: UnquoteError_ -> String
unquoteErrorNameString = defaultErrorNameString

-- | Print list of errors.

helpErrors :: String
helpErrors = unlines $ concat
  [ [ "Agda's errors:"
    , ""
    ]
  , sort $ map errorNameString [minBound..maxBound]
  ]

-- * Print error messages
------------------------------------------------------------------------

verbalizeNotAValidLetBinding :: NotAValidLetBinding -> String
verbalizeNotAValidLetBinding = \case
  AbstractNotAllowed     -> "`abstract` not allowed in let bindings"
  MacrosNotAllowed       -> "Macros cannot be defined in let bindings"
  MissingRHS             -> "Missing right hand side in let binding"
  NotAValidLetPattern    -> "Not a valid let pattern"
  WhereClausesNotAllowed -> "`where` clauses not allowed in let bindings"
  -- These cannot be triggered:
  -- CopatternsNotAllowed   -> "Copatterns not allowed in let bindings"
  -- EllipsisNotAllowed     -> "`...` not allowed in let bindings"
  -- WithPatternsNotAllowed -> "`with` patterns not allowed in let bindings"

verbalizeNotAValidLetExpression :: NotAValidLetExpression -> String
verbalizeNotAValidLetExpression = \case
  MissingBody -> "Missing body in let-expression"

-- Instances
------------------------------------------------------------------------

deriving via (FiniteEnumeration (Maybe a))
  instance (Bounded a, Enum a) => Enum (Maybe a)
deriving via (FiniteEnumeration (Maybe a))
  instance (Bounded a, Enum a) => Bounded (Maybe a)

instance NFData ErasedDatatypeReason
instance NFData NotAllowedInDotPatterns
instance NFData NotAValidLetBinding
instance NFData NotAValidLetExpression
