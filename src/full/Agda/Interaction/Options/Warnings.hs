
module Agda.Interaction.Options.Warnings
       (
         WarningMode (..)
       , warningSet
       , warn2Error
       , lensSingleWarning
       , defaultWarningSet
       , allWarnings
       , usualWarnings
       , noWarnings
       , unsolvedWarnings
       , unusedImportsWarnings
       , incompleteMatchWarnings
       , errorWarnings
       , exactSplitWarnings
       , defaultWarningMode
       , WarningModeError(..)
       , prettyWarningModeError
       , warningModeUpdate
       , warningSets
       , WarningName (..)
       , warningNameToString
       , string2WarningName
       , usageWarning
       )
where

import Control.DeepSeq
import Control.Monad ( guard, when )
import Control.Monad.Except ( throwError )

import qualified Data.HashMap.Strict as HMap
import Data.List ( stripPrefix, intercalate, partition, sort )
import Data.Set  ( Set )
import qualified Data.Set as Set
import Data.Text ( Text )
import qualified Data.Text as Text

import GHC.Generics (Generic)

import Agda.Utils.Either ( maybeToEither )
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Singleton ( singleton )
import Agda.Utils.Tuple ( (&&&) )

import Agda.Utils.Impossible


-- | A @WarningMode@ has two components: a set of warnings to be displayed
-- and a flag stating whether warnings should be turned into fatal errors.
data WarningMode = WarningMode
  { _warningSet :: Set WarningName
      -- ^ Invariant: When 'UnusedImportsAll_' is in the warning set, so must be 'UnusedImports_'.
  , _warn2Error :: Bool
  } deriving (Eq, Show, Generic)

instance NFData WarningMode

-- Lenses

warningSet :: Lens' WarningMode (Set WarningName)
warningSet f o = (\ ws -> o { _warningSet = ws }) <$> f (_warningSet o)

warn2Error :: Lens' WarningMode Bool
warn2Error f o = (\ ws -> o { _warn2Error = ws }) <$> f (_warn2Error o)

lensSingleWarning :: WarningName -> Lens' WarningMode Bool
lensSingleWarning w = warningSet . contains w

-- | The @defaultWarningMode@ is a curated set of warnings covering non-fatal
-- errors and disabling style-related ones

defaultWarningSet :: String
defaultWarningSet = "warn"

defaultWarningMode :: WarningMode
defaultWarningMode = WarningMode ws False where
  ws = fst $ fromMaybe __IMPOSSIBLE__ $ lookup defaultWarningSet warningSets

-- | Some warnings are errors and cannot be turned off.
data WarningModeError
  = Unknown Text
      -- ^ Unknown warning.
  | NoNoError Text
      -- ^ Warning that cannot be disabled.
  | NoUnusedImportsAll
      -- ^ @-WnoUnusedImports=all@ is not supported, use @-WnoUnusedImports@ instead.
  deriving (Show, Generic)

instance NFData WarningModeError

prettyWarningModeError :: WarningModeError -> Text
prettyWarningModeError = \case
  Unknown   w -> Text.concat [ "Unknown warning flag: ", w, "." ]
  NoNoError w -> Text.concat
    [ "You may only turn off benign warnings. The warning "
    , w
    , " is a non-fatal error and thus cannot be ignored."
    ]
  NoUnusedImportsAll ->
    "-WnoUnusedImports=all is not supported, use -WnoUnusedImports instead."

-- | From user-given directives we compute WarningMode updates
type WarningModeUpdate = WarningMode -> WarningMode

-- | @warningModeUpdate str@ computes the action of @str@ over the current
-- @WarningMode@: it may reset the set of warnings, add or remove a specific
-- flag or demand that any warning be turned into an error

warningModeUpdate :: String -> Either WarningModeError WarningModeUpdate
warningModeUpdate str = case str of
  "error"   -> pure $ set warn2Error True
  "noerror" -> pure $ set warn2Error False
  _ | Just ws <- fst <$> lookup str warningSets
            -> pure $ set warningSet ws
  _ -> case stripPrefix "no" str of
    Nothing   -> do
      wname <- stringToWarningName str
      let
        wnames = case wname of
          -- Invariant: when UnusedImportsAll_ is in the warning set,
          -- so must be UnusedImports_
          UnusedImportsAll_ -> unusedImportsWarnings
          w -> singleton w
      pure $ over warningSet $ (`Set.union` wnames)
    Just str' -> do
      wname <- stringToWarningName str'
      when (wname `elem` errorWarnings) $
        throwError $ NoNoError $ Text.pack str'
      wnames <- case wname of
        UnusedImports_    -> pure unusedImportsWarnings
        UnusedImportsAll_ -> throwError NoUnusedImportsAll
        w -> pure $ singleton w
      pure $ over warningSet $ (Set.\\ wnames)
  where
    stringToWarningName :: String -> Either WarningModeError WarningName
    stringToWarningName str = maybeToEither (Unknown $ Text.pack str) $ string2WarningName str


-- | Common sets of warnings

warningSets :: [(String, (Set WarningName, String))]
warningSets = [ ("all"   , (allWarnings, "All of the existing warnings"))
              , ("warn"  , (usualWarnings, "Default warning level"))
              , ("ignore", (errorWarnings, "Ignore all the benign warnings"))
              ]

noWarnings :: Set WarningName
noWarnings = Set.empty

unsolvedWarnings :: Set WarningName
unsolvedWarnings = Set.fromList
                 [ UnsolvedMetaVariables_
                 , UnsolvedInteractionMetas_
                 , UnsolvedConstraints_
                 ]

incompleteMatchWarnings :: Set WarningName
incompleteMatchWarnings = Set.fromList [ CoverageIssue_ ]

errorWarnings :: Set WarningName
errorWarnings = Set.fromList
  [ CoverageIssue_
  , InvalidCharacterLiteral_
  , MissingDefinitions_
  , MissingDataDeclaration_
  , NotAllowedInMutual_
  , NotStrictlyPositive_
  , ConstructorDoesNotFitInData_
  , OverlappingTokensWarning_
  , PragmaCompiled_
  , SafeFlagPostulate_
  , SafeFlagPragma_
  , SafeFlagNonTerminating_
  , SafeFlagTerminating_
  , SafeFlagWithoutKFlagPrimEraseEquality_
  , SafeFlagNoPositivityCheck_
  , SafeFlagPolarity_
  , SafeFlagNoUniverseCheck_
  , SafeFlagEta_
  , SafeFlagInjective_
  , SafeFlagNoCoverageCheck_
  , TerminationIssue_
  , TooManyArgumentsToSort_
  , UnsolvedMetaVariables_
  , UnsolvedInteractionMetas_
  , UnsolvedConstraints_
  , InfectiveImport_
  , CoInfectiveImport_
  -- Andreas, 2024-02-15: the following warning used to be a GenericWarning (not an error warning).
  -- Maybe revisit.
  -- , ConfluenceCheckingIncompleteBecauseOfMeta_
  , RewriteNonConfluent_
  , RewriteMaybeNonConfluent_
  , RewriteAmbiguousRules_
  , RewriteMissingRule_
  , LetBoundLocalRewrite_
  , LambdaBoundLocalRewrite_
  , LocalRewriteOutsideTelescope_
  , TopLevelPolarity_

  -- Recoverable parse errors
  , MismatchedBrackets_

  -- Recoverable scope-checking errors
  , HiddenNotInArgumentPosition_
  , InstanceNotInArgumentPosition_
  , MacroInLetBindings_
  , AbstractInLetBindings_
  , IllegalDeclarationInDataDefinition_
  ]

allWarnings :: Set WarningName
allWarnings = Set.fromList [minBound..maxBound]

usualWarnings :: Set WarningName
usualWarnings =
  allWarnings Set.\\ exactSplitWarnings Set.\\ Set.fromList
    [ UnknownFixityInMixfixDecl_
    , ShadowingInTelescope_
    , UnusedImports_
    , UnusedImportsAll_
    ]

-- | Warnings enabled by @--exact-split@.
--
exactSplitWarnings :: Set WarningName
exactSplitWarnings = Set.fromList
  [ CoverageNoExactSplit_
  , InlineNoExactSplit_
  ]

-- | Both of these warnings are disabled by @-WnoUnusedImports@.
unusedImportsWarnings :: Set WarningName
unusedImportsWarnings = Set.fromList [ UnusedImports_, UnusedImportsAll_ ]

-- | The @WarningName@ data enumeration is meant to have a one-to-one correspondance
-- to existing warnings in the codebase.

data WarningName
  -- Option Warnings
  = OptionRenamed_
  | WarningProblem_
      -- ^ Some warning could not be set or unset.
  -- Parser Warnings
  | OverlappingTokensWarning_
  | MisplacedAttributes_
  | UnknownPolarity_
  | UnknownAttribute_
  | UnsupportedAttribute_
  | MultipleAttributes_
  | MismatchedBrackets_
  -- Library Warnings
  | LibUnknownField_
  -- Nicifer Warnings
  | DivergentModalityInClause_
  | EmptyAbstract_
  | EmptyConstructor_
  | EmptyField_
  | EmptyGeneralize_
  | EmptyInstance_
  | EmptyMacro_
  | EmptyMutual_
  | EmptyPostulate_
  | EmptyPrimitive_
  | EmptyPrivate_
  | EmptyRewritePragma_
  | EmptyWhere_
  | EmptyPolarityPragma_
  | HiddenGeneralize_
  | InvalidCatchallPragma_
  | InvalidConstructorBlock_
  | InvalidCoverageCheckPragma_
  | InvalidDataOrRecDefParameter_
  | InvalidNoPositivityCheckPragma_
  | InvalidNoUniverseCheckPragma_
  | DuplicateRecordDirective_
  | InvalidTerminationCheckPragma_
  | InvalidTacticAttribute_
  | MissingDataDeclaration_
  | MissingDefinitions_
  | NotAllowedInMutual_
  | OpenImportAbstract_
  | OpenImportPrivate_
  | PolarityPragmasButNotPostulates_
  | PragmaCompiled_
  | PragmaNoTerminationCheck_
  | ShadowingInTelescope_
  | UnknownFixityInMixfixDecl_
  | UnknownNamesInFixityDecl_
  | UnknownNamesInPolarityPragmas_
  | UselessAbstract_
  | UselessImport_
  | UselessInstance_
  | UselessMacro_
  | UselessPrivate_
  -- Scope and Type Checking Warnings
  | AbsurdPatternRequiresAbsentRHS_
  | AsPatternShadowsConstructorOrPatternSynonym_
  | PatternShadowsConstructor_
  | CantGeneralizeOverSorts_
  | ClashesViaRenaming_                -- issue #4154
  | CoverageIssue_
  | CoverageNoExactSplit_
  | InlineNoExactSplit_
  | DeprecationWarning_
  | DuplicateUsing_
  | FixingCohesion_
  | FixingPolarity_
  | FixingRelevance_
  -- TODO: linearity
  -- -- | FixingQuantity_
  | FixityInRenamingModule_
  | InvalidCharacterLiteral_
  | UnusedImports_
  | UnusedImportsAll_
  | UselessPragma_
  | IllegalDeclarationInDataDefinition_
  | IllformedAsClause_
  | InstanceArgWithExplicitArg_
  | InstanceWithExplicitArg_
  | InstanceNoOutputTypeName_
  | InteractionMetaBoundaries_
  | InversionDepthReached_
  | ModuleDoesntExport_
  | NotInScope_
  | NotStrictlyPositive_
  | ConstructorDoesNotFitInData_
  | CoinductiveEtaRecord_
  | UnsupportedIndexedMatch_
  | OldBuiltin_
  | BuiltinDeclaresIdentifier_
  | PlentyInHardCompileTimeMode_
  | PragmaCompileErased_
  | PragmaCompileList_
  | PragmaCompileMaybe_
  | PragmaCompileUnparsable_
  | PragmaCompileWrong_
  | PragmaCompileWrongName_
  | PragmaExpectsDefinedSymbol_
  | PragmaExpectsUnambiguousConstructorOrFunction_
  | PragmaExpectsUnambiguousProjectionOrFunction_
  | UnknownJSPrimitive_
  | NoMain_
  | NotARewriteRule_
  | RewriteLHSNotDefinitionOrConstructor_
  | RewriteVariablesNotBoundByLHS_
  | RewriteVariablesBoundMoreThanOnce_
  | RewriteVariablesBoundInSingleton_
  | RewriteLHSReduces_
  | RewriteHeadSymbolIsProjectionLikeFunction_
  | RewriteHeadSymbolIsTypeConstructor_
  | RewriteHeadSymbolContainsMetas_
  | RewriteConstructorParametersNotGeneral_
  | RewriteContainsUnsolvedMetaVariables_
  | RewriteBlockedOnProblems_
  | RewriteRequiresDefinitions_
  | RewriteDoesNotTargetRewriteRelation_
  | RewriteBeforeFunctionDefinition_
  | RewriteBeforeMutualFunctionDefinition_
  | ConfluenceCheckingIncompleteBecauseOfMeta_
  | ConfluenceForCubicalNotSupported_
  | RewriteMaybeNonConfluent_
  | RewriteNonConfluent_
  | RewriteAmbiguousRules_
  | RewriteMissingRule_
  | DuplicateRewriteRule_
  | LetBoundLocalRewrite_
  | LambdaBoundLocalRewrite_
  | LocalRewriteOutsideTelescope_
  | SafeFlagEta_
  | SafeFlagInjective_
  | SafeFlagNoCoverageCheck_
  | SafeFlagNonTerminating_
  | SafeFlagNoPositivityCheck_
  | SafeFlagNoUniverseCheck_
  | SafeFlagPolarity_
  | SafeFlagPostulate_
  | SafeFlagPragma_
  | SafeFlagTerminating_
  | SafeFlagWithoutKFlagPrimEraseEquality_
  | TerminationIssue_
  | TooManyArgumentsToSort_
  | UnreachableClauses_
  | UnsolvedConstraints_
  | UnsolvedInteractionMetas_
  | UnsolvedMetaVariables_
  | UselessHiding_
  | UselessInline_
  | UselessPatternDeclarationForRecord_
  | UselessPublic_
  | UselessTactic_
  | UserWarning_
  | InvalidDisplayForm_
  | UnusedVariablesInDisplayForm_
  | RewritesNothing_
  | WithClauseProjectionFixityMismatch_
  | WithoutKFlagPrimEraseEquality_
  | ConflictingPragmaOptions_
  | WrongInstanceDeclaration_
  | TooManyPolarities_
  | TopLevelPolarity_
  -- Checking consistency of options
  | CoInfectiveImport_
  | InfectiveImport_
  -- Record field warnings
  | DuplicateFields_
  | TooManyFields_
  -- Opaque/unfolding
  | MissingTypeSignatureForOpaque_
  | NotAffectedByOpaque_
  | UnfoldingWrongName_
  | UnfoldTransparentName_
  | UselessOpaque_
  -- Recoverable scope checking errors
  | HiddenNotInArgumentPosition_
  | InstanceNotInArgumentPosition_
  | MacroInLetBindings_
  | AbstractInLetBindings_
  -- Cubical
  | FaceConstraintCannotBeHidden_
  | FaceConstraintCannotBeNamed_
  -- Backends
  | CustomBackendWarning_
  deriving (Eq, Ord, Show, Read, Enum, Bounded, Generic)

instance NFData WarningName

-- | The flag corresponding to a warning is precisely the name of the constructor
-- minus the trailing underscore.

string2WarningName :: String -> Maybe WarningName
string2WarningName = (`HMap.lookup` warnings) where
  warnings = HMap.fromList $ map (\x -> (warningNameToString x, x)) [minBound..maxBound]

warningNameToString :: WarningName -> String
warningNameToString = \case
  UnusedImportsAll_ -> "UnusedImports=all"
  w -> initWithDefault __IMPOSSIBLE__ $ show w

-- | @warningUsage@ generated using @warningNameDescription@

usageWarning :: String
usageWarning = intercalate "\n"
  [ "The -W or --warning option can be used to disable or enable\
    \ different warnings. The flag -W error (or --warning=error)\
    \ can be used to turn all warnings into errors, while -W noerror\
    \ turns this off again."
  , ""
  , "A group of warnings can be enabled by -W group, where group is\
    \ one of the following:"
  , ""
  , untable (fmap (fst &&& snd . snd) warningSets)

  , "Individual benign warnings can be turned on and off by -W Name and\
    \ -W noName, respectively, where Name comes from the following\
    \ list (warnings marked with 'd' are turned on by default):"
  , ""
  , warningTable True benign

  , "Error warnings are always on and cannot be turned off:"
  , ""
  , warningTable False severe
  ]

  where

    (severe, benign) = partition (`Set.member` errorWarnings) [minBound..maxBound]

    warningTable printD ws =
      untable $ forMaybe ws $ \ w ->
        let wnd = warningNameDescription w in
        ( warningNameToString w
        , applyWhen printD ((if w `Set.member` usualWarnings then "d" else " ") ++)
          " " ++
          wnd
        ) <$ guard (not $ null wnd)

    untable :: [(String, String)] -> String
    untable rows =
      let len = maximum (map (length . fst) rows) in
      unlines $ for (sort rows) $ \ (hdr, cnt) ->
        concat [ hdr, replicate (1 + len - length hdr) ' ', cnt ]


-- | @WarningName@ descriptions used for generating usage information
-- Leave String empty to skip that name.
--
-- The description should be a completion of the sentence "This warning is about ...".
-- So, typically the subject is in plural.
--
warningNameDescription :: WarningName -> String
warningNameDescription = \case
  -- Option Warnings
  OptionRenamed_                   -> "Renamed options."
  WarningProblem_                  -> "Problems with switching warnings."
  -- Parser Warnings
  OverlappingTokensWarning_        -> "Multi-line comments spanning one or more literate text blocks."
  MisplacedAttributes_             -> "Attributes where they are not supported."
  UnknownPolarity_                 -> "Unknown polarities."
  UnknownAttribute_                -> "Unknown attributes."
  UnsupportedAttribute_            -> "Unsupported attributes."
  MultipleAttributes_              -> "Multiple attributes."
  MismatchedBrackets_              -> "Mismatched brackets."
  -- Library Warnings
  LibUnknownField_                 -> "Unknown fields in library files."
  -- Nicifer Warnings
  DivergentModalityInClause_       -> "Divergent modalities in function clauses."
  EmptyAbstract_                   -> "Empty `abstract' blocks."
  EmptyConstructor_                -> "Empty `constructor' blocks."
  EmptyField_                      -> "Empty `field` blocks."
  EmptyGeneralize_                 -> "Empty `variable' blocks."
  EmptyInstance_                   -> "Empty `instance' blocks."
  EmptyMacro_                      -> "Empty `macro' blocks."
  EmptyMutual_                     -> "Empty `mutual' blocks."
  EmptyPostulate_                  -> "Empty `postulate' blocks."
  EmptyPrimitive_                  -> "Empty `primitive' blocks."
  EmptyPrivate_                    -> "Empty `private' blocks."
  EmptyRewritePragma_              -> "Empty `REWRITE' pragmas."
  EmptyWhere_                      -> "Empty `where' blocks."
  EmptyPolarityPragma_             -> "`POLARITY' pragmas giving no polarities."
  HiddenGeneralize_                -> "Hidden identifiers in variable blocks."
  InvalidCatchallPragma_           -> "`CATCHALL' pragmas before a non-function clause."
  InvalidConstructorBlock_         -> "`constructor' blocks outside of `interleaved mutual' blocks."
  InvalidCoverageCheckPragma_      -> "Coverage checking pragmas before non-function or `mutual' blocks."
  InvalidDataOrRecDefParameter_    -> "Invalid decorations of parameters of a `data' or `record' definition (that is separate of the `data' or `record' declaration)."
  InvalidNoPositivityCheckPragma_  -> "Positivity checking pragmas before non-`data', `record' or `mutual' blocks."
  InvalidNoUniverseCheckPragma_    -> "Universe checking pragmas before non-`data' or `record' declaration."
  DuplicateRecordDirective_        -> "Conflicting directives in a record declaration."
  InvalidTacticAttribute_          -> "Misplaced @(tactic ...) attributes."
  InvalidTerminationCheckPragma_   -> "Termination checking pragmas before non-function or `mutual' blocks."
  MissingDataDeclaration_          -> "Constructor definitions not associated to a data declaration."
  MissingDefinitions_              -> "Declarations not associated to a definition."
  NotAllowedInMutual_              -> "Declarations not allowed in a mutual block."
  OpenImportAbstract_              -> "`open' or `import' statements in 'abstract' blocks."
  OpenImportPrivate_               -> "`open' or `import' statements in 'private' blocks."
  PolarityPragmasButNotPostulates_ -> "Polarity pragmas for non-postulates."
  PragmaCompiled_                  -> "'COMPILE' pragmas in safe mode."
  PragmaNoTerminationCheck_        -> "`NO_TERMINATION_CHECK' pragmas; such are deprecated."
  ShadowingInTelescope_            -> "Repeated variable names in telescopes."
  UnknownFixityInMixfixDecl_       -> "Mixfix names without an associated fixity declaration."
  UnknownNamesInFixityDecl_        -> "Names not declared in the same scope as their syntax or fixity declaration."
  UnknownNamesInPolarityPragmas_   -> "Names not declared in the same scope as their polarity pragmas."
  UselessAbstract_                 -> "`abstract' blocks where they have no effect."
  UselessHiding_                   -> "Names in `hiding' directive that are anyway not imported."
  UselessImport_                   -> "`import' statements that do not bring anything into scope."
  UselessInline_                   -> "`INLINE' pragmas where they have no effect."
  UselessInstance_                 -> "`instance' blocks where they have no effect."
  UselessMacro_                    -> "`macro' blocks where they have no effect."
  UselessPrivate_                  -> "`private' blocks where they have no effect."
  UselessPublic_                   -> "`public' directives that have no effect."
  UselessPatternDeclarationForRecord_ -> "`pattern' attributes where they have no effect."
  UselessTactic_                   -> "`@tactic` attributes where they have no effect."
  -- Scope and Type Checking Warnings
  AbsurdPatternRequiresAbsentRHS_  -> "Clauses with an absurd pattern that have a right hand side."
  AsPatternShadowsConstructorOrPatternSynonym_ -> "@-patterns that shadow constructors or pattern synonyms."
  PatternShadowsConstructor_       -> "Pattern variables that shadow constructors."
  CantGeneralizeOverSorts_         -> "Attempts to generalize over sort metas in 'variable' declaration."
  ClashesViaRenaming_              -> "Clashes introduced by `renaming'."  -- issue #4154
  CoverageIssue_                   -> "Failed coverage checks."
  CoverageNoExactSplit_            -> "Failed exact split checks."
  InlineNoExactSplit_              -> "Failed exact split checks after inlining record constructors."
  DeprecationWarning_              -> "Deprecated features."
  -- TODO: linearity
  -- FixingQuantity_                  -> "Correcting invalid user-written quantity."
  FixingRelevance_                 -> "Correcting invalid user-written relevance attribute."
  FixingCohesion_                  -> "Correcting invalid user-written cohesion attribute."
  FixingPolarity_                  -> "Correcting invalid user-written polarity attribute."
  InvalidCharacterLiteral_         -> "Illegal character literals."
  UselessPragma_                   -> "Pragmas that get ignored."
  IllegalDeclarationInDataDefinition_ -> "Declarations not allowed in `data' definitions."
  IllformedAsClause_               -> "Illformed `as'-clauses in `import' statements."
  InstanceNoOutputTypeName_        -> "Instance arguments whose type does not end in a named or variable type; those are never considered by instance search."
  InstanceArgWithExplicitArg_      -> "Instance arguments with explicit arguments; those are never considered by instance search."
  InstanceWithExplicitArg_         -> "`instance` declarations with explicit arguments; those are never considered by instance search."
  InversionDepthReached_           -> "Inversions of pattern-matching failures due to exhausted inversion depth."
  ModuleDoesntExport_              -> "Imported names that are not actually exported."
  DuplicateUsing_                  -> "Repeated names in using directive."
  FixityInRenamingModule_          -> "Fixity annotations in `renaming' directive for `module'."
  NotInScope_                      -> "Out of scope names."
  NotStrictlyPositive_             -> "Failed strict positivity checks."
  ConstructorDoesNotFitInData_     -> "Failed constructor size checks."
  CoinductiveEtaRecord_            -> "Record type declared as both coinductive and having eta-equality."
  UnsupportedIndexedMatch_         -> "Failures to compute full equivalence when splitting on indexed family."
  OldBuiltin_                      -> "Deprecated `BUILTIN' pragmas."
  BuiltinDeclaresIdentifier_       -> "`BUILTIN' pragmas that declare a new identifier but have been given an existing one."
  PlentyInHardCompileTimeMode_     -> "Uses of @ω or @plenty in hard compile-time mode."
  PragmaCompileErased_             -> "`COMPILE' pragmas targeting an erased symbol."
  PragmaCompileList_               -> "`COMPILE GHC' pragmas for lists."
  PragmaCompileMaybe_              -> "`COMPILE GHC' pragmas for `MAYBE'."
  PragmaCompileUnparsable_         -> "Unparsable `COMPILE GHC' pragmas."
  PragmaCompileWrong_              -> "Ill-formed `COMPILE GHC' pragmas."
  PragmaCompileWrongName_          -> "`COMPILE' pragmas referring to identifiers that are neither definitions nor constructors.'"
  PragmaExpectsDefinedSymbol_      -> "Pragmas referring to identifiers that are not defined symbols."
  PragmaExpectsUnambiguousConstructorOrFunction_    -> "Pragmas referring to identifiers that are not unambiguous constructors or functions.'"
  PragmaExpectsUnambiguousProjectionOrFunction_     -> "Pragmas referring to identifiers that are not unambiguous projections or functions.'"
  UnknownJSPrimitive_              -> "Primitive compiled to `Undefined' by the JS backend because it is not in the list of known primitives."
  NoMain_                          -> "Compilation of modules that do not define `main'."
  NotARewriteRule_                 -> "`REWRITE pragmas referring to identifiers that are neither definitions nor constructors.'"
  RewriteLHSNotDefinitionOrConstructor_             -> "Rewrite rule head symbol is not a defined symbol or constructor."
  RewriteVariablesNotBoundByLHS_                    -> "Rewrite rule does not bind all of its variables."
  RewriteVariablesBoundMoreThanOnce_                -> "Constructor-headed rewrite rule has non-linear parameters."
  RewriteVariablesBoundInSingleton_                 -> "Rewrite rule binds some variables in possibly definitionally singular contexts."
  RewriteLHSReduces_                                -> "Rewrite rule LHS is not in weak-head normal form."
  RewriteHeadSymbolIsProjectionLikeFunction_        -> "Rewrite rule head symbol is a projection-like function."
  RewriteHeadSymbolIsTypeConstructor_               -> "Rewrite rule head symbol is a type constructor."
  RewriteHeadSymbolContainsMetas_                   -> "Definition of rewrite rule head symbol contains unsolved metas."
  RewriteConstructorParametersNotGeneral_           -> "Constructor-headed rewrite rule parameters are not fully general."
  RewriteContainsUnsolvedMetaVariables_             -> "Rewrite rule contains unsolved metas."
  RewriteBlockedOnProblems_                         -> "Checking rewrite rule blocked by unsolved constraint."
  RewriteRequiresDefinitions_                       -> "Checking rewrite rule blocked by missing definition."
  RewriteDoesNotTargetRewriteRelation_              -> "Rewrite rule does not target the rewrite relation."
  RewriteBeforeFunctionDefinition_                  -> "Rewrite rule is not yet defined."
  RewriteBeforeMutualFunctionDefinition_            -> "Mutually declaration with the rewrite rule is not yet defined."
  ConfluenceCheckingIncompleteBecauseOfMeta_ -> "Incomplete confluence checks because of unsolved metas."
  ConfluenceForCubicalNotSupported_ -> "Incomplete confluence checks because of `--cubical'."
  RewriteMaybeNonConfluent_        -> "Failed local confluence checks while computing overlap."
  RewriteNonConfluent_             -> "Failed local confluence checks while joining critical pairs."
  RewriteAmbiguousRules_           -> "Failed global confluence checks because of overlapping rules."
  RewriteMissingRule_              -> "Failed global confluence checks because of missing rule."
  DuplicateRewriteRule_            -> "Duplicate rewrite rules."
  LetBoundLocalRewrite_            -> "Let-binding annotated with '@rew'."
  LambdaBoundLocalRewrite_         -> "Binding '@rew' argument with a lambda."
  LocalRewriteOutsideTelescope_    -> "'@rew' arguments are (currently) only allowed in module telescopes."
  SafeFlagEta_                     -> "`ETA' pragmas with the safe flag."
  SafeFlagInjective_               -> "`INJECTIVE' pragmas with the safe flag."
  SafeFlagNoCoverageCheck_         -> "`NON_COVERING` pragmas with the safe flag."
  SafeFlagNonTerminating_          -> "`NON_TERMINATING' pragmas with the safe flag."
  SafeFlagNoPositivityCheck_       -> "`NO_POSITIVITY_CHECK' pragmas with the safe flag."
  SafeFlagNoUniverseCheck_         -> "`NO_UNIVERSE_CHECK' pragmas with the safe flag."
  SafeFlagPolarity_                -> "`POLARITY' pragmas with the safe flag."
  SafeFlagPostulate_               -> "`postulate' blocks with the safe flag."
  SafeFlagPragma_                  -> "Unsafe `OPTIONS' pragmas with the safe flag."
  SafeFlagTerminating_             -> "`TERMINATING' pragmas with the safe flag."
  SafeFlagWithoutKFlagPrimEraseEquality_ -> "`primEraseEquality' used with the safe and without-K flags."
  ConflictingPragmaOptions_        -> "Conflicting pragma options."
  TerminationIssue_                -> "Failed termination checks."
  UnreachableClauses_              -> "Unreachable function clauses."
  UnsolvedConstraints_             -> "Unsolved constraints."
  UnsolvedInteractionMetas_        -> "Unsolved interaction meta variables."
  InteractionMetaBoundaries_       -> "Interaction meta variables that have unsolved boundary constraints."
  UnsolvedMetaVariables_           -> "Unsolved meta variables."
  UserWarning_                     -> "User-defined warnings via one of the 'WARNING_ON_*' pragmas."
  InvalidDisplayForm_              -> "Invalid display forms."
  UnusedVariablesInDisplayForm_    -> "Bound but unused variables in display forms."
  TooManyArgumentsToSort_          -> "Extra arguments given to a sort."
  RewritesNothing_                 -> "`rewrite' clauses that do not fire."
  WithClauseProjectionFixityMismatch_ -> "With clauses using projections in different fixities than their parent clauses."
  WithoutKFlagPrimEraseEquality_   -> "Uses of `primEraseEquality' with the without-K flags."
  WrongInstanceDeclaration_        -> "Instances that do not adhere to the required format."
  TooManyPolarities_               -> "Too many polarities given in POLARITY pragma."
  TopLevelPolarity_                -> "Declaring definitions with an explicit polarity annotation."
  UnusedImports_                   -> "Identifiers brought into scope but never referenced."
  UnusedImportsAll_                -> "Identifiers brought into scope but never referenced (strict version)."
  -- Checking consistency of options
  CoInfectiveImport_               -> "Importing a file not using e.g. `--safe'  from one which does."
  InfectiveImport_                 -> "Importing a file using e.g. `--cubical' into one which does not."
  -- Record field warnings
  DuplicateFields_                 -> "Record expressions with duplicate field names."
  TooManyFields_                   -> "Record expressions with invalid field names."
  -- Opaque/unfolding warnings
  MissingTypeSignatureForOpaque_   -> "Definitions that are `abstract` or `opaque` yet lack type signatures."
  NotAffectedByOpaque_             -> "Declarations unaffected by enclosing `opaque` blocks."
  UnfoldingWrongName_              -> "Names in `unfolding` clause that are not unambiguous functions."
  UnfoldTransparentName_           -> "Non-`opaque` names mentioned in an `unfolding` clause."
  UselessOpaque_                   -> "`opaque` blocks that have no effect."

  -- Recoverable scope-checking errors
  HiddenNotInArgumentPosition_     -> "Hidden argument with no matching function."
  InstanceNotInArgumentPosition_   -> "Instance argument with no matching function."
  MacroInLetBindings_              -> "Macros can not be let-bound."
  AbstractInLetBindings_           -> "Let bindings can not contain abstract declarations."

  -- Cubical
  FaceConstraintCannotBeHidden_    -> "Face constraint patterns that are given as implicit arguments."
  FaceConstraintCannotBeNamed_     -> "Face constraint patterns that are given as named arguments."
  -- Backends
  CustomBackendWarning_            -> "Custom warnings from backends."
