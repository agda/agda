
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
       , incompleteMatchWarnings
       , errorWarnings
       , exactSplitWarnings
       , defaultWarningMode
       , WarningModeError(..)
       , prettyWarningModeError
       , warningModeUpdate
       , warningSets
       , WarningName (..)
       , warningName2String
       , string2WarningName
       , usageWarning
       )
where

import Control.Arrow ( (&&&) )
import Control.DeepSeq
import Control.Monad ( guard, when )

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.HashMap.Strict as HMap
import Data.List ( stripPrefix, intercalate, partition, sort )

import GHC.Generics (Generic)

import Agda.Utils.Either ( maybeToEither )
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe

import Agda.Utils.Impossible


-- | A @WarningMode@ has two components: a set of warnings to be displayed
-- and a flag stating whether warnings should be turned into fatal errors.
data WarningMode = WarningMode
  { _warningSet :: Set WarningName
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
data WarningModeError = Unknown String | NoNoError String

prettyWarningModeError :: WarningModeError -> String
prettyWarningModeError = \case
  Unknown str -> concat [ "Unknown warning flag: ", str, "." ]
  NoNoError str -> concat [ "You may only turn off benign warnings. The warning "
                          , str
                          ," is a non-fatal error and thus cannot be ignored." ]

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
      wname :: WarningName <- maybeToEither (Unknown str) $ string2WarningName str
      pure (over warningSet $ Set.insert wname)
    Just str' -> do
      wname :: WarningName <- maybeToEither (Unknown str') $ string2WarningName str'
      when (wname `elem` errorWarnings) (Left (NoNoError str'))
      pure (over warningSet $ Set.delete wname)

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
  , MissingDeclarations_
  , NotAllowedInMutual_
  , NotStrictlyPositive_
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
  , UnsolvedMetaVariables_
  , UnsolvedInteractionMetas_
  , UnsolvedConstraints_
  , InfectiveImport_
  , CoInfectiveImport_
  , RewriteNonConfluent_
  , RewriteMaybeNonConfluent_
  , RewriteAmbiguousRules_
  , RewriteMissingRule_
  ]

allWarnings :: Set WarningName
allWarnings = Set.fromList [minBound..maxBound]

usualWarnings :: Set WarningName
usualWarnings =
  allWarnings Set.\\ exactSplitWarnings Set.\\ Set.fromList
    [ UnknownFixityInMixfixDecl_
    , ShadowingInTelescope_
    ]

-- | Warnings enabled by @--exact-split@.
--
exactSplitWarnings :: Set WarningName
exactSplitWarnings = Set.fromList
  [ CoverageNoExactSplit_
  , InlineNoExactSplit_
  ]

-- | The @WarningName@ data enumeration is meant to have a one-to-one correspondance
-- to existing warnings in the codebase.

data WarningName
  -- Option Warnings
  = OptionRenamed_
  -- Parser Warnings
  | OverlappingTokensWarning_
  | UnsupportedAttribute_
  | MultipleAttributes_
  -- Library Warnings
  | LibUnknownField_
  -- Nicifer Warnings
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
  | HiddenGeneralize_
  | InvalidCatchallPragma_
  | InvalidConstructor_
  | InvalidConstructorBlock_
  | InvalidCoverageCheckPragma_
  | InvalidNoPositivityCheckPragma_
  | InvalidNoUniverseCheckPragma_
  | InvalidRecordDirective_
  | InvalidTerminationCheckPragma_
  | MissingDeclarations_
  | MissingDefinitions_
  | NotAllowedInMutual_
  | OpenPublicAbstract_
  | OpenPublicPrivate_
  | PolarityPragmasButNotPostulates_
  | PragmaCompiled_
  | PragmaNoTerminationCheck_
  | ShadowingInTelescope_
  | UnknownFixityInMixfixDecl_
  | UnknownNamesInFixityDecl_
  | UnknownNamesInPolarityPragmas_
  | UselessAbstract_
  | UselessInstance_
  | UselessPrivate_
  -- Scope and Type Checking Warnings
  | AbsurdPatternRequiresNoRHS_
  | AsPatternShadowsConstructorOrPatternSynonym_
  | PatternShadowsConstructor_
  | CantGeneralizeOverSorts_
  | ClashesViaRenaming_                -- issue #4154
  | CoverageIssue_
  | CoverageNoExactSplit_
  | InlineNoExactSplit_
  | DeprecationWarning_
  | DuplicateUsing_
  | FixityInRenamingModule_
  | InvalidCharacterLiteral_
  | UselessPragma_
  | GenericWarning_
  | IllformedAsClause_
  | InstanceArgWithExplicitArg_
  | InstanceWithExplicitArg_
  | InstanceNoOutputTypeName_
  | InteractionMetaBoundaries_
  | InversionDepthReached_
  | ModuleDoesntExport_
  | NoGuardednessFlag_
  | NotInScope_
  | NotStrictlyPositive_
  | UnsupportedIndexedMatch_
  | OldBuiltin_
  | PlentyInHardCompileTimeMode_
  | PragmaCompileErased_
  | RewriteMaybeNonConfluent_
  | RewriteNonConfluent_
  | RewriteAmbiguousRules_
  | RewriteMissingRule_
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
  | UnreachableClauses_
  | UnsolvedConstraints_
  | UnsolvedInteractionMetas_
  | UnsolvedMetaVariables_
  | UselessHiding_
  | UselessInline_
  | UselessPatternDeclarationForRecord_
  | UselessPublic_
  | UserWarning_
  | WithoutKFlagPrimEraseEquality_
  | WrongInstanceDeclaration_
  -- Checking consistency of options
  | CoInfectiveImport_
  | InfectiveImport_
  -- Record field warnings
  | DuplicateFields_
  | TooManyFields_
  -- Opaque/unfolding
  | NotAffectedByOpaque_
  | UnfoldTransparentName_
  | UselessOpaque_
  -- Cubical
  | FaceConstraintCannotBeHidden_
  | FaceConstraintCannotBeNamed_
  deriving (Eq, Ord, Show, Read, Enum, Bounded, Generic)

instance NFData WarningName

-- | The flag corresponding to a warning is precisely the name of the constructor
-- minus the trailing underscore.

string2WarningName :: String -> Maybe WarningName
string2WarningName = (`HMap.lookup` warnings) where
  warnings = HMap.fromList $ map (\x -> (warningName2String x, x)) [minBound..maxBound]

warningName2String :: WarningName -> String
warningName2String = initWithDefault __IMPOSSIBLE__ . show

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
        ( warningName2String w
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
  -- Parser Warnings
  OverlappingTokensWarning_        -> "Multi-line comments spanning one or more literate text blocks."
  UnsupportedAttribute_            -> "Unsupported attributes."
  MultipleAttributes_              -> "Multiple attributes."
  -- Library Warnings
  LibUnknownField_                 -> "Unknown fields in library files."
  -- Nicifer Warnings
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
  HiddenGeneralize_                -> "Hidden identifiers in variable blocks."
  InvalidCatchallPragma_           -> "`CATCHALL' pragmas before a non-function clause."
  InvalidConstructor_              -> "`constructor' blocks that contain declarations other than type signatures for constructors."
  InvalidConstructorBlock_         -> "`constructor' blocks outside of `interleaved mutual' blocks."
  InvalidCoverageCheckPragma_      -> "Coverage checking pragmas before non-function or `mutual' blocks."
  InvalidNoPositivityCheckPragma_  -> "Positivity checking pragmas before non-`data', `record' or `mutual' blocks."
  InvalidNoUniverseCheckPragma_    -> "Universe checking pragmas before non-`data' or `record' declaration."
  InvalidRecordDirective_          -> "Record directives outside of record definitions or below field declarations."
  InvalidTerminationCheckPragma_   -> "Termination checking pragmas before non-function or `mutual' blocks."
  MissingDeclarations_             -> "Definitions not associated to a declaration."
  MissingDefinitions_              -> "Declarations not associated to a definition."
  NotAllowedInMutual_              -> "Declarations not allowed in a mutual block."
  OpenPublicAbstract_              -> "'open public' directives in 'abstract' blocks."
  OpenPublicPrivate_               -> "'open public' directives in 'private' blocks."
  PolarityPragmasButNotPostulates_ -> "Polarity pragmas for non-postulates."
  PragmaCompiled_                  -> "'COMPILE' pragmas in safe mode."
  PragmaNoTerminationCheck_        -> "`NO_TERMINATION_CHECK' pragmas; such are deprecated."
  ShadowingInTelescope_            -> "Repeated variable names in telescopes."
  UnknownFixityInMixfixDecl_       -> "Mixfix names without an associated fixity declaration."
  UnknownNamesInFixityDecl_        -> "Names not declared in the same scope as their syntax or fixity declaration."
  UnknownNamesInPolarityPragmas_   -> "Names not declared in the same scope as their polarity pragmas."
  UselessAbstract_                 -> "`abstract' blocks where they have no effect."
  UselessHiding_                   -> "Names in `hiding' directive that are anyway not imported."
  UselessInline_                   -> "`INLINE' pragmas where they have no effect."
  UselessInstance_                 -> "`instance' blocks where they have no effect."
  UselessPrivate_                  -> "`private' blocks where they have no effect."
  UselessPublic_                   -> "`public' blocks where they have no effect."
  UselessPatternDeclarationForRecord_ -> "`pattern' attributes where they have no effect."
  -- Scope and Type Checking Warnings
  AbsurdPatternRequiresNoRHS_      -> "Clauses with an absurd pattern that have a right hand side."
  AsPatternShadowsConstructorOrPatternSynonym_ -> "@-patterns that shadow constructors or pattern synonyms."
  PatternShadowsConstructor_       -> "Pattern variables that shadow constructors."
  CantGeneralizeOverSorts_         -> "Attempts to generalize over sort metas in 'variable' declaration."
  ClashesViaRenaming_              -> "Clashes introduced by `renaming'."  -- issue #4154
  CoverageIssue_                   -> "Failed coverage checks."
  CoverageNoExactSplit_            -> "Failed exact split checks."
  InlineNoExactSplit_              -> "Failed exact split checks after inlining record constructors."
  DeprecationWarning_              -> "Deprecated features."
  InvalidCharacterLiteral_         -> "Illegal character literals."
  UselessPragma_                   -> "Pragmas that get ignored."
  GenericWarning_                  -> ""
  IllformedAsClause_               -> "Illformed `as'-clauses in `import' statements."
  InstanceNoOutputTypeName_        -> "Instance arguments whose type does not end in a named or variable type; those are never considered by instance search."
  InstanceArgWithExplicitArg_      -> "Instance arguments with explicit arguments; those are never considered by instance search."
  InstanceWithExplicitArg_         -> "`instance` declarations with explicit arguments; those are never considered by instance search."
  InversionDepthReached_           -> "Inversions of pattern-matching failures due to exhausted inversion depth."
  NoGuardednessFlag_               -> "Coinductive records without --guardedness flag."
  ModuleDoesntExport_              -> "Imported names that are not actually exported."
  DuplicateUsing_                  -> "Repeated names in using directive."
  FixityInRenamingModule_          -> "Fixity annotations in `renaming' directive for `module'."
  NotInScope_                      -> "Out of scope names."
  NotStrictlyPositive_             -> "Failed strict positivity checks."
  UnsupportedIndexedMatch_         -> "Failures to compute full equivalence when splitting on indexed family."
  OldBuiltin_                      -> "Deprecated `BUILTIN' pragmas."
  PlentyInHardCompileTimeMode_     -> "Uses of @ω or @plenty in hard compile-time mode."
  PragmaCompileErased_             -> "`COMPILE' pragmas targeting an erased symbol."
  RewriteMaybeNonConfluent_        -> "Failed local confluence checks while computing overlap."
  RewriteNonConfluent_             -> "Failed local confluence checks while joining critical pairs."
  RewriteAmbiguousRules_           -> "Failed global confluence checks because of overlapping rules."
  RewriteMissingRule_              -> "Failed global confluence checks because of missing rule."
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
  TerminationIssue_                -> "Failed termination checks."
  UnreachableClauses_              -> "Unreachable function clauses."
  UnsolvedConstraints_             -> "Unsolved constraints."
  UnsolvedInteractionMetas_        -> "Unsolved interaction meta variables."
  InteractionMetaBoundaries_       -> "Interaction meta variables that have unsolved boundary constraints."
  UnsolvedMetaVariables_           -> "Unsolved meta variables."
  UserWarning_                     -> "User-defined warnings via one of the 'WARNING_ON_*' pragmas."
  WithoutKFlagPrimEraseEquality_   -> "Uses of `primEraseEquality' with the without-K flags."
  WrongInstanceDeclaration_        -> "Instances that do not adhere to the required format."
  -- Checking consistency of options
  CoInfectiveImport_               -> "Importing a file not using e.g. `--safe'  from one which does."
  InfectiveImport_                 -> "Importing a file using e.g. `--cubical' into one which does not."
  -- Record field warnings
  DuplicateFields_                 -> "Record expressions with duplicate field names."
  TooManyFields_                   -> "Record expressions with invalid field names."
  -- Opaque/unfolding warnings
  NotAffectedByOpaque_             -> "Declarations unaffected by enclosing `opaque` blocks."
  UnfoldTransparentName_           -> "Non-`opaque` names mentioned in an `unfolding` clause."
  UselessOpaque_                   -> "`opaque` blocks that have no effect."
  -- Cubical
  FaceConstraintCannotBeHidden_    -> "Face constraint patterns that are given as implicit arguments."
  FaceConstraintCannotBeNamed_     -> "Face constraint patterns that are given as named arguments."
