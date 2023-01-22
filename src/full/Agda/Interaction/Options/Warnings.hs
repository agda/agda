
module Agda.Interaction.Options.Warnings
       (
         WarningMode (..)
       , warningSet
       , warn2Error
       , defaultWarningSet
       , allWarnings
       , usualWarnings
       , noWarnings
       , unsolvedWarnings
       , incompleteMatchWarnings
       , errorWarnings
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

import Text.Read ( readMaybe )
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.HashMap.Strict as HMap
import Data.List ( stripPrefix, intercalate )

import GHC.Generics (Generic)

import Agda.Utils.Either ( maybeToEither )
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe

import Agda.Utils.Impossible
import Agda.Utils.Functor


-- | A @WarningMode@ has two components: a set of warnings to be displayed
-- and a flag stating whether warnings should be turned into fatal errors.
data WarningMode = WarningMode
  { _warningSet :: Set WarningName
  , _warn2Error :: Bool
  } deriving (Eq, Show, Generic)

instance NFData WarningMode

warningSet :: Lens' (Set WarningName) WarningMode
warningSet f o = (\ ws -> o { _warningSet = ws }) <$> f (_warningSet o)

warn2Error :: Lens' Bool WarningMode
warn2Error f o = (\ ws -> o { _warn2Error = ws }) <$> f (_warn2Error o)

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
  , GenericNonFatalError_
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
usualWarnings = allWarnings Set.\\ Set.fromList
              [ UnknownFixityInMixfixDecl_
              , CoverageNoExactSplit_
              , ShadowingInTelescope_
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
  | CantGeneralizeOverSorts_
  | ClashesViaRenaming_                -- issue #4154
  | CoverageIssue_
  | CoverageNoExactSplit_
  | DeprecationWarning_
  | DuplicateUsing_
  | FixityInRenamingModule_
  | GenericNonFatalError_
  | GenericUseless_
  | GenericWarning_
  | IllformedAsClause_
  | InstanceArgWithExplicitArg_
  | InstanceWithExplicitArg_
  | InstanceNoOutputTypeName_
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
  | DuplicateFieldsWarning_
  | TooManyFieldsWarning_
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
    \ list (warnings marked with 'd' are turned on by default, and 'b'\
    \ stands for \"benign warning\"):"
  , ""
  , untable $ forMaybe [minBound..maxBound] $ \ w ->
    let wnd = warningNameDescription w in
    ( warningName2String w
    , (if w `Set.member` usualWarnings then "d" else " ") ++
      (if not (w `Set.member` errorWarnings) then "b" else " ") ++
      " " ++
      wnd
    ) <$ guard (not $ null wnd)
  ]

  where

    untable :: [(String, String)] -> String
    untable rows =
      let len = maximum (map (length . fst) rows) in
      unlines $ for rows $ \ (hdr, cnt) ->
        concat [ hdr, replicate (1 + len - length hdr) ' ', cnt ]

-- | @WarningName@ descriptions used for generating usage information
-- Leave String empty to skip that name.

warningNameDescription :: WarningName -> String
warningNameDescription = \case
  -- Option Warnings
  OptionRenamed_                   -> "Renamed options."
  -- Parser Warnings
  OverlappingTokensWarning_        -> "Multi-line comments spanning one or more literate text blocks."
  UnsupportedAttribute_            -> "Unsupported attributes."
  MultipleAttributes_              -> "Multiple attributes."
  -- Library Warnings
  LibUnknownField_                 -> "Unknown field in library file."
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
  InvalidConstructor_              -> "`constructor' blocks may only contain type signatures for constructors."
  InvalidConstructorBlock_         -> "No `constructor' blocks outside of `interleaved mutual' blocks."
  InvalidCoverageCheckPragma_      -> "Coverage checking pragmas before non-function or `mutual' blocks."
  InvalidNoPositivityCheckPragma_  -> "No positivity checking pragmas before non-`data', `record' or `mutual' blocks."
  InvalidNoUniverseCheckPragma_    -> "No universe checking pragmas before non-`data' or `record' declaration."
  InvalidRecordDirective_          -> "No record directive outside of record definition / below field declarations."
  InvalidTerminationCheckPragma_   -> "Termination checking pragmas before non-function or `mutual' blocks."
  MissingDeclarations_             -> "Definitions not associated to a declaration."
  MissingDefinitions_              -> "Declarations not associated to a definition."
  NotAllowedInMutual_              -> "Declarations not allowed in a mutual block."
  OpenPublicAbstract_              -> "'open public' directive in an 'abstract' block."
  OpenPublicPrivate_               -> "'open public' directive in a 'private' block."
  PolarityPragmasButNotPostulates_ -> "Polarity pragmas for non-postulates."
  PragmaCompiled_                  -> "'COMPILE' pragmas not allowed in safe mode."
  PragmaNoTerminationCheck_        -> "`NO_TERMINATION_CHECK' pragmas are deprecated"
  ShadowingInTelescope_            -> "Repeated variable name in telescope."
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
  AbsurdPatternRequiresNoRHS_      -> "A clause with an absurd pattern does not need a Right Hand Side."
  AsPatternShadowsConstructorOrPatternSynonym_ -> "@-patterns that shadow constructors or pattern synonyms."
  CantGeneralizeOverSorts_         -> "Attempt to generalize over sort metas in 'variable' declaration."
  ClashesViaRenaming_              -> "Clashes introduced by `renaming'."  -- issue #4154
  CoverageIssue_                   -> "Failed coverage checks."
  CoverageNoExactSplit_            -> "Failed exact split checks."
  DeprecationWarning_              -> "Feature deprecation."
  GenericNonFatalError_            -> ""
  GenericUseless_                  -> "Useless code."
  GenericWarning_                  -> ""
  IllformedAsClause_               -> "Illformed `as'-clauses in `import' statements."
  InstanceNoOutputTypeName_        -> "instance arguments whose type does not end in a named or variable type are never considered by instance search."
  InstanceArgWithExplicitArg_      -> "instance arguments with explicit arguments are never considered by instance search."
  InstanceWithExplicitArg_         -> "`instance` declarations with explicit arguments are never considered by instance search."
  InversionDepthReached_           -> "Inversions of pattern-matching failed due to exhausted inversion depth."
  NoGuardednessFlag_               -> "Coinductive record but no --guardedness flag."
  ModuleDoesntExport_              -> "Imported name is not actually exported."
  DuplicateUsing_                  -> "Repeated names in using directive."
  FixityInRenamingModule_          -> "Found fixity annotation in renaming directive for module."
  NotInScope_                      -> "Out of scope name."
  NotStrictlyPositive_             -> "Failed strict positivity checks."
  UnsupportedIndexedMatch_         -> "Failed to compute full equivalence when splitting on indexed family."
  OldBuiltin_                      -> "Deprecated `BUILTIN' pragmas."
  PlentyInHardCompileTimeMode_     -> "Use of @ω or @plenty in hard compile-time mode."
  PragmaCompileErased_             -> "`COMPILE' pragma targeting an erased symbol."
  RewriteMaybeNonConfluent_        -> "Failed local confluence check while computing overlap."
  RewriteNonConfluent_             -> "Failed local confluence check while joining critical pairs."
  RewriteAmbiguousRules_           -> "Failed global confluence check because of overlapping rules."
  RewriteMissingRule_              -> "Failed global confluence check because of missing rule."
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
  UnsolvedMetaVariables_           -> "Unsolved meta variables."
  UserWarning_                     -> "User-defined warning added using one of the 'WARNING_ON_*' pragmas."
  WithoutKFlagPrimEraseEquality_   -> "`primEraseEquality' usages with the without-K flags."
  WrongInstanceDeclaration_        -> "Instances that do not adhere to the required format."
  -- Checking consistency of options
  CoInfectiveImport_               -> "Importing a file not using e.g. `--safe'  from one which does."
  InfectiveImport_                 -> "Importing a file using e.g. `--cubical' into one which doesn't."
  -- Record field warnings
  DuplicateFieldsWarning_          -> "Record expression with duplicate field names."
  TooManyFieldsWarning_            -> "Record expression with invalid field names."
