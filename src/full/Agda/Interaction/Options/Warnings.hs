
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
       , errorWarnings
       , defaultWarningMode
       , warningModeUpdate
       , warningSets
       , WarningName (..)
       , warningName2String
       , string2WarningName
       , usageWarning
       )
where

import Control.Arrow ( (&&&) )
import Control.Monad ( guard )

import Data.Traversable ( for )

import Text.Read ( readMaybe )
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe ( fromMaybe )
import Data.List ( stripPrefix, intercalate )

import Agda.Utils.Lens
import Agda.Utils.Maybe

import Agda.Utils.Impossible


-- | A @WarningMode@ has two components: a set of warnings to be displayed
-- and a flag stating whether warnings should be turned into fatal errors.
data WarningMode = WarningMode
  { _warningSet :: Set WarningName
  , _warn2Error :: Bool
  } deriving (Eq, Show)

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

-- | @warningModeUpdate str@ computes the action of @str@ over the current
-- @WarningMode@: it may reset the set of warnings, add or remove a specific
-- flag or demand that any warning be turned into an error

warningModeUpdate :: String -> Maybe (WarningMode -> WarningMode)
warningModeUpdate str = case str of
  "error"   -> Just $ set warn2Error True
  "noerror" -> Just $ set warn2Error False
  _ | Just ws <- fst <$> lookup str warningSets
            -> Just $ set warningSet ws
  _ -> case stripPrefix "no" str of
    Just str' -> (over warningSet . Set.delete) <$> string2WarningName str'
    Nothing   -> (over warningSet . Set.insert) <$> string2WarningName str

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

errorWarnings :: Set WarningName
errorWarnings = Set.fromList
  [ CoverageIssue_
  , GenericNonFatalError_
  , MissingDefinitions_
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
  , TerminationIssue_
  , UnsolvedMetaVariables_
  , UnsolvedInteractionMetas_
  , UnsolvedConstraints_
  , InfectiveImport_
  , CoInfectiveImport_
  , RewriteNonConfluent_
  , RewriteMaybeNonConfluent_
  ]

allWarnings :: Set WarningName
allWarnings = Set.fromList [minBound..maxBound]

usualWarnings :: Set WarningName
usualWarnings = allWarnings Set.\\ Set.fromList
              [ UnknownFixityInMixfixDecl_
              , CoverageNoExactSplit_
              ]

-- | The @WarningName@ data enumeration is meant to have a one-to-one correspondance
-- to existing warnings in the codebase.

data WarningName
  =
  -- Parser Warnings
    OverlappingTokensWarning_
  -- Library Warnings
  | LibUnknownField_
  -- Nicifer Warnings
  | EmptyAbstract_
  | EmptyGeneralize_
  | EmptyInstance_
  | EmptyMacro_
  | EmptyMutual_
  | EmptyPostulate_
  | EmptyPrimitive_
  | EmptyPrivate_
  | EmptyRewritePragma_
  | InvalidCatchallPragma_
  | InvalidNoPositivityCheckPragma_
  | InvalidNoUniverseCheckPragma_
  | InvalidTerminationCheckPragma_
  | MissingDefinitions_
  | NotAllowedInMutual_
  | PolarityPragmasButNotPostulates_
  | PragmaCompiled_
  | PragmaNoTerminationCheck_
  | UnknownFixityInMixfixDecl_
  | UnknownNamesInFixityDecl_
  | UnknownNamesInPolarityPragmas_
  | UselessAbstract_
  | UselessInstance_
  | UselessPrivate_
  -- Scope and Type Checking Warnings
  | AbsurdPatternRequiresNoRHS_
  | CantGeneralizeOverSorts_
  | CoverageIssue_
  | CoverageNoExactSplit_
  | DeprecationWarning_
  | GenericNonFatalError_
  | GenericWarning_
  | IllformedAsClause_
  | InstanceArgWithExplicitArg_
  | InstanceWithExplicitArg_
  | InstanceNoOutputTypeName_
  | InversionDepthReached_
  | ModuleDoesntExport_
  | NotStrictlyPositive_
  | OldBuiltin_
  | RewriteMaybeNonConfluent_
  | RewriteNonConfluent_
  | SafeFlagNoPositivityCheck_
  | SafeFlagNonTerminating_
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
  | UselessInline_
  | UselessPublic_
  | UserWarning_
  | WithoutKFlagPrimEraseEquality_
  | WrongInstanceDeclaration_
  -- Checking consistency of options
  | CoInfectiveImport_
  | InfectiveImport_
  deriving (Eq, Ord, Show, Read, Enum, Bounded)

-- | The flag corresponding to a warning is precisely the name of the constructor
-- minus the trailing underscore.

-- sorry
string2WarningName :: String -> Maybe WarningName
string2WarningName = readMaybe . (++ "_")

warningName2String :: WarningName -> String
warningName2String = init . show

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
  , "Individual warnings can be turned on and off by -W Name and\
    \ -W noName respectively. The flags available are:"
  , ""
  , untable $ forMaybe [minBound..maxBound] $ \ w ->
    let wnd = warningNameDescription w in
    (warningName2String w, wnd) <$ guard (not $ null wnd)
  ]

  where

    untable :: [(String, String)] -> String
    untable rows =
      let len = maximum (map (length . fst) rows) in
      unlines $ flip map rows $ \ (hdr, cnt) ->
        concat [ hdr, replicate (1 + len - length hdr) ' ', cnt ]

-- | @WarningName@ descriptions used for generating usage information
-- Leave String empty to skip that name.

warningNameDescription :: WarningName -> String
warningNameDescription w = case w of
  -- Parser Warnings
  OverlappingTokensWarning_        -> "Multi-line comments spanning one or more literate text blocks."
  -- Library Warnings
  LibUnknownField_                 -> "Unknown field in library file."
  -- Nicifer Warnings
  EmptyAbstract_                   -> "Empty `abstract' blocks."
  EmptyGeneralize_                 -> "Empty `variable' blocks."
  EmptyInstance_                   -> "Empty `instance' blocks."
  EmptyMacro_                      -> "Empty `macro' blocks."
  EmptyMutual_                     -> "Empty `mutual' blocks."
  EmptyPostulate_                  -> "Empty `postulate' blocks."
  EmptyPrimitive_                  -> "Empty `primitive' blocks."
  EmptyPrivate_                    -> "Empty `private' blocks."
  EmptyRewritePragma_              -> "Empty `REWRITE' pragmas."
  InvalidCatchallPragma_           -> "`CATCHALL' pragmas before a non-function clause."
  InvalidNoPositivityCheckPragma_  -> "No positivity checking pragmas before non-`data', `record' or `mutual' blocks."
  InvalidNoUniverseCheckPragma_    -> "No universe checking pragmas before non-`data' or `record' declaration."
  InvalidTerminationCheckPragma_   -> "Termination checking pragmas before non-function or `mutual' blocks."
  MissingDefinitions_              -> "Declarations not associated to a definition."
  NotAllowedInMutual_              -> "Declarations not allowed in a mutual block."
  PolarityPragmasButNotPostulates_ -> "Polarity pragmas for non-postulates."
  PragmaCompiled_                  -> "'COMPILE' pragmas not allowed in safe mode."
  PragmaNoTerminationCheck_        -> "`NO_TERMINATION_CHECK' pragmas are deprecated"
  UnknownFixityInMixfixDecl_       -> "Mixfix names without an associated fixity declaration."
  UnknownNamesInFixityDecl_        -> "Names not declared in the same scope as their syntax or fixity declaration."
  UnknownNamesInPolarityPragmas_   -> "Names not declared in the same scope as their polarity pragmas."
  UselessAbstract_                 -> "`abstract' blocks where they have no effect."
  UselessInline_                   -> "`INLINE' pragmas where they have no effect."
  UselessInstance_                 -> "`instance' blocks where they have no effect."
  UselessPrivate_                  -> "`private' blocks where they have no effect."
  UselessPublic_                   -> "`public' blocks where they have no effect."
  -- Scope and Type Checking Warnings
  AbsurdPatternRequiresNoRHS_      -> "A clause with an absurd pattern does not need a Right Hand Side."
  CantGeneralizeOverSorts_         -> "Attempt to generalize over sort metas in 'variable' declaration."
  CoverageIssue_                   -> "Failed coverage checks."
  CoverageNoExactSplit_            -> "Failed exact split checks."
  DeprecationWarning_              -> "Feature deprecation."
  GenericNonFatalError_            -> ""
  GenericWarning_                  -> ""
  IllformedAsClause_               -> "Illformed `as'-clauses in `import' statements."
  InstanceNoOutputTypeName_        -> "instance arguments whose type does not end in a named or variable type are never considered by instance search."
  InstanceArgWithExplicitArg_      -> "instance arguments with explicit arguments are never considered by instance search."
  InstanceWithExplicitArg_         -> "`instance` declarations with explicit arguments are never considered by instance search."
  InversionDepthReached_           -> "Inversions of pattern-matching failed due to exhausted inversion depth."
  ModuleDoesntExport_              -> "Imported name is not actually exported."
  NotStrictlyPositive_             -> "Failed strict positivity checks."
  OldBuiltin_                      -> "Deprecated `BUILTIN' pragmas."
  RewriteMaybeNonConfluent_      -> "Failed confluence checks while computing overlap."
  RewriteNonConfluent_           -> "Failed confluence checks while joining critical pairs."
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
  WrongInstanceDeclaration_        -> "Terms marked as eligible for instance search should end with a name."
  -- Checking consistency of options
  CoInfectiveImport_               -> "Importing a file not using e.g. `--safe'  from one which does."
  InfectiveImport_                 -> "Importing a file using e.g. `--cubical' into one which doesn't."
