-- | Provide names for the errors Agda throws.Options/Er

module Agda.Interaction.Options.Errors where

import Control.DeepSeq        ( NFData )
import Data.List              ( sort )
import Generic.Data           ( FiniteEnumeration(..) )
import GHC.Generics           ( Generic )

import Agda.Syntax.Common     ( ConstructorOrPatternSynonym(..) )

import Agda.Utils.Function    ( applyWhenJust )
import Agda.Utils.List        ( initWithDefault )
import Agda.Utils.Impossible  ( __IMPOSSIBLE__ )

-- | Extra information for error 'CannotQuoteTerm'.

data CannotQuoteTerm
  = CannotQuoteTermHidden
  | CannotQuoteTermNothing
  deriving (Show, Generic, Enum, Bounded)

-- | What kind of declaration?
--
--   See also 'Agda.Syntax.Concrete.Definitions.Types.DataRecOrFun'.

data DataRecOrFun_
  = DataName_  -- ^ Name of a data type.
  | RecName_   -- ^ Name of a record type.
  | FunName_   -- ^ Name of a function.
  deriving (Show, Generic, Enum, Bounded)

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
  = ExecError_             ExecError_
  | GHCBackendError_       GHCBackendError_
  | ImpossibleConstructor_ NegativeUnification_
  | InteractionError_      InteractionError_
  | JSBackendError_        JSBackendError_
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
  | BackendDoesNotSupportOnlyScopeChecking_
  | BadArgumentsToPatternSynonym_
  | BuiltinInParameterisedModule_
  | BuiltinMustBeConstructor_
  | CannotEliminateWithPattern_
  | CannotEliminateWithProjection_
  | CannotGenerateHCompClause_
  | CannotGenerateTransportClause_
  | CannotQuote_ CannotQuote_
  | CannotQuoteTerm_ CannotQuoteTerm
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
  | CopatternHeadNotProjection_
  | CubicalCompilationNotSupported_
  | CubicalPrimitiveNotFullyApplied_
  | CyclicModuleDependency_
  | DeBruijnIndexOutOfScope_
  | DeclarationsAfterTopLevelModule_
  | DefinitionInDifferentModule_
  | DefinitionIsErased_
  | DefinitionIsIrrelevant_
  | DoNotationError_
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
  | IdiomBracketError_
  | InvalidDottedExpression_
  | IllTypedPatternAfterWithAbstraction_
  | IllegalDeclarationBeforeTopLevelModule_
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
  | InvalidPun_ ConstructorOrPatternSynonym
  | InvalidTypeSort_
  | LibTooFarDown_
  | LiteralTooBig_
  | MacroResultTypeMismatch_
  | MetaCannotDependOn_
  | MetaErasedSolution_
  | MetaIrrelevantSolution_
  | MismatchedProjectionsError_
  | MissingTypeSignature_ DataRecOrFun_
  | ModuleArityMismatch_
  | ModuleDefinedInOtherFile_
  | ModuleNameDoesntMatchFileName_
  | ModuleNameUnexpected_
  | MultipleFixityDecls_
  | MultiplePolarityPragmas_
  | ExplicitPolarityVsPragma_
  | ConstructorNameOfNonRecord_
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
  | OpenEverythingInRecordWhere_
  | OverlappingProjects_
  | PatternInPathLambda_
  | PatternInSystem_
  | PatternSynonymArgumentShadows_ ConstructorOrPatternSynonym
  | PrivateRecordField_
  | ProjectionIsIrrelevant_
  | QualifiedLocalModule_
  | QuantityMismatch_
  | RecursiveRecordNeedsInductivity_
  | ReferencesFutureVariables_
  | RelevanceMismatch_
  | RepeatedNamesInImportDirective_
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
  | SplitOnUnusablePolarity_
  | TacticAttributeNotAllowed_
  | TooFewArgumentsToPatternSynonym_
  | TooFewPatternsInWithClause_
  | TooManyFields_
  | TooManyPatternsInWithClause_
  | TooManyPolarities_
  | TriedToCopyConstrainedPrim_
  | InvalidInstanceHeadType_
  | UnboundVariablesInPatternSynonym_
  | UnequalCohesion_
  | UnequalFiniteness_
  | UnequalHiding_
  | UnequalLevel_
  | UnequalQuantity_
  | UnequalRelevance_
  | UnequalPolarity_
  | UnequalSorts_
  | UnequalTerms_
  | UnexpectedModalityAnnotationInParameter_
  | UnexpectedParameter_
  | UnexpectedTypeSignatureForParameter_
  | UnexpectedWithPatterns_
  | UnknownBackend_
  | UnusableAtModality_
  | UnusedVariableInPatternSynonym_
  | VariableIsErased_
  | VariableIsIrrelevant_
  | VariableIsOfUnusableCohesion_
  | VariableIsOfUnusablePolarity_
  | WithClausePatternMismatch_
  | WithOnFreeVariable_
  | WrongAnnotationInLambda_
  | WrongArgInfoForPrimitive_
  | WrongCohesionInLambda_
  | WrongPolarityInLambda_
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
  | DisallowedInterleavedMutual_
  | DuplicateAnonDeclaration_
  | DuplicateDefinition_
  | InvalidMeasureMutual_
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

data JSBackendError_
  = BadCompilePragma_
  deriving (Show, Generic)
  deriving (Enum, Bounded) via (FiniteEnumeration JSBackendError_)

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

data CannotQuote_
  = CannotQuoteAmbiguous_
  | CannotQuoteExpression_
  | CannotQuoteHidden_
  | CannotQuoteNothing_
  | CannotQuotePattern_
  deriving (Show, Generic, Enum, Bounded)

data ExecError_
  = ExeNotTrusted_
  | ExeNotFound_
  | ExeNotExecutable_
  deriving (Show, Generic, Enum, Bounded)

data UnquoteError_
  = CannotDeclareHiddenFunction_
  | ConInsteadOfDef_
  | DefInsteadOfCon_
  | MissingDeclaration_
  | MissingDefinition_
  | NakedUnquote_
  | NonCanonical_
  | BlockedOnMeta_
  | PatLamWithoutClauses_
  | StaleMeta_
  deriving (Show, Generic, Enum, Bounded)

-- * Printing error names
------------------------------------------------------------------------

defaultErrorNameString :: Show a => a -> String
defaultErrorNameString = initWithDefault __IMPOSSIBLE__ . show

erasedDatatypeReasonString :: ErasedDatatypeReason -> String
erasedDatatypeReasonString = show

errorNameString :: ErrorName -> String
errorNameString = \case
  ExecError_              err -> "Exec." ++ execErrorNameString err
  GHCBackendError_        err -> "GHCBackend." ++ ghcBackendErrorNameString err
  ImpossibleConstructor_  err -> "ImpossibleConstructor." ++ negativeUnificationErrorNameString err
  InteractionError_       err -> "Interaction." ++ interactionErrorNameString err
  JSBackendError_         err -> "JSBackend." ++ jsBackendErrorNameString err
  NicifierError_          err -> "Syntax." ++ declarationExceptionNameString err
  SplitError_             err -> "SplitError." ++ splitErrorNameString err
  UnquoteError_           err -> "Unquote." ++ unquoteErrorNameString err
  CannotQuote_             err -> "CannotQuote." ++ cannotQuoteNameString err
  CannotQuoteTerm_         err -> "CannotQuoteTerm." ++ cannotQuoteTermNameString err
  InvalidPun_              err -> "InvalidPun." ++ constructorOrPatternSynonymNameString err
  MissingTypeSignature_    err -> "MissingTypeSignature." ++ dataRecOrFunString err
  NotAllowedInDotPatterns_ err -> "NotAllowedInDotPatterns." ++ notAllowedInDotPatternsString err
  NotAValidLetBinding_    merr -> applyWhenJust merr (\ err hd -> hd ++ "." ++ notAValidLetBindingString err) "NotAValidLetBinding"
  NotAValidLetExpression_  err -> "NotAValidLetExpression." ++ notAValidLetExpressionString err
  PatternSynonymArgumentShadows_ err -> "PatternSynonymArgumentShadows." ++ constructorOrPatternSynonymNameString err
  err -> defaultErrorNameString err

constructorOrPatternSynonymNameString :: ConstructorOrPatternSynonym -> String
constructorOrPatternSynonymNameString = \case
  IsConstructor    -> "Constructor"
  IsPatternSynonym -> "PatternSynonym"

dataRecOrFunString :: DataRecOrFun_ -> String
dataRecOrFunString = \case
  DataName_ -> "Data"
  RecName_  -> "Record"
  FunName_  -> "Function"

declarationExceptionNameString :: DeclarationException_ -> String
declarationExceptionNameString = \case
  AmbiguousConstructorN_ -> "AmbiguousConstructor"
  err -> defaultErrorNameString err

ghcBackendErrorNameString :: GHCBackendError_ -> String
ghcBackendErrorNameString = \case
  NotAHaskellType_ err -> "NotAHaskellType." ++ notAHaskellTypeErrorNameString err
  err -> defaultErrorNameString err

jsBackendErrorNameString :: JSBackendError_ -> String
jsBackendErrorNameString = defaultErrorNameString

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

cannotQuoteNameString :: CannotQuote_ -> String
cannotQuoteNameString = \case
  CannotQuoteAmbiguous_  -> "Ambiguous"
  CannotQuoteExpression_ -> "Expression"
  CannotQuoteHidden_     -> "Hidden"
  CannotQuoteNothing_    -> "Nothing"
  CannotQuotePattern_    -> "Pattern"

cannotQuoteTermNameString :: CannotQuoteTerm -> String
cannotQuoteTermNameString = \case
  CannotQuoteTermHidden      -> "Hidden"
  CannotQuoteTermNothing     -> "Nothing"

execErrorNameString :: ExecError_ -> String
execErrorNameString = defaultErrorNameString

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

instance NFData CannotQuoteTerm
instance NFData ErasedDatatypeReason
instance NFData NotAllowedInDotPatterns
instance NFData NotAValidLetBinding
instance NFData NotAValidLetExpression
