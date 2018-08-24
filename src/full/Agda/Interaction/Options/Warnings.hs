{-# LANGUAGE CPP #-}

module Agda.Interaction.Options.Warnings
       (
         WarningMode (..)
       , warningSet
       , warn2Error
       , defaultWarningSet
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
import Data.Maybe ( fromMaybe, catMaybes )
import Data.List ( stripPrefix, intercalate )

import Agda.Utils.Lens

#include "undefined.h"
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
              , ("ignore", (noWarnings, "Ignore all warnings"))
              ]

noWarnings :: Set WarningName
noWarnings = Set.empty

allWarnings :: Set WarningName
allWarnings = Set.fromList [minBound..maxBound]

usualWarnings :: Set WarningName
usualWarnings = allWarnings Set.\\ Set.fromList
              [ UnknownFixityInMixfixDecl_ ]

-- | The @WarningName@ data enumeration is meant to have a one-to-one correspondance
-- to existing warnings in the codebase.

data WarningName
  =
  -- Parser Warning
    OverlappingTokensWarning_
  -- Nicifer Warning
  | EmptyAbstract_
  | EmptyInstance_
  | EmptyMacro_
  | EmptyMutual_
  | EmptyPostulate_
  | EmptyPrivate_
  | InvalidCatchallPragma_
  | InvalidNoUniverseCheckPragma_
  | InvalidTerminationCheckPragma_
  | InvalidNoPositivityCheckPragma_
  | MissingDefinitions_
  | PolarityPragmasButNotPostulates_
  | UnknownFixityInMixfixDecl_
  | UnknownNamesInFixityDecl_
  | UnknownNamesInPolarityPragmas_
  | UselessAbstract_
  | UselessInstance_
  | UselessPrivate_
  -- Scope and Type Checking Warning
  | OldBuiltin_
  | EmptyRewritePragma_
  | UselessPublic_
  | UnreachableClauses_
  | UselessInline_
  | GenericWarning_
  | DeprecationWarning_
  | InversionDepthReached_
  | TerminationIssue_
  | CoverageIssue_
  | CoverageNoExactSplit_
  | NotStrictlyPositive_
  | UnsolvedMetaVariables_
  | UnsolvedInteractionMetas_
  | UnsolvedConstraints_
  | GenericNonFatalError_
  | SafeFlagPostulate_
  | SafeFlagPragma_
  | SafeFlagNonTerminating_
  | SafeFlagTerminating_
  | SafeFlagPrimTrustMe_
  | SafeFlagNoPositivityCheck_
  | SafeFlagPolarity_
  | SafeFlagNoUniverseCheck_
  | UserWarning_
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
  -- Looks like CPP doesn't like multiline string literals
  [ concat [ "The -W or --warning option can be used to disable or enable "
           , "different warnings. The flag -W error (or --warning=error) "
           , "can be used to turn all warnings into errors, while -W noerror "
           , "turns this off again."
           ]
  , ""
  , concat [ "A group of warnings can be enabled by -W group, where group is "
           , "one of the following:"
           ]
  , ""
  , untable (fmap (fst &&& snd . snd) warningSets)
  , concat [ "Individual warnings can be turned on and off by -W Name and "
           , "-W noName respectively. The flags available are:"
           ]
  , ""
  , untable $ catMaybes $ flip map [minBound..maxBound] $ \ w ->
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
  OverlappingTokensWarning_        -> "Multi-line comments spanning one or more literate text blocks."
  -- Nicifer Warning
  EmptyAbstract_                   -> "Empty `abstract' blocks."
  EmptyInstance_                   -> "Empty `instance' blocks."
  EmptyMacro_                      -> "Empty `macro' blocks."
  EmptyMutual_                     -> "Empty `mutual' blocks."
  EmptyPostulate_                  -> "Empty `postulate' blocks."
  EmptyPrivate_                    -> "Empty `private' blocks."
  InvalidCatchallPragma_           -> "`CATCHALL' pragmas before a non-function clause."
  InvalidNoPositivityCheckPragma_  -> "No positivity checking pragmas before non-`data', `record' or `mutual' blocks."
  InvalidNoUniverseCheckPragma_    -> "No universe checking pragmas before non-`data' or `record' declaration."
  InvalidTerminationCheckPragma_   -> "Termination checking pragmas before non-function or `mutual' blocks."
  MissingDefinitions_              -> "Declarations not associated to a definition."
  PolarityPragmasButNotPostulates_ -> "Polarity pragmas for non-postulates."
  UnknownFixityInMixfixDecl_       -> "Mixfix names without an associated fixity declaration."
  UnknownNamesInFixityDecl_        -> "Names not declared in the same scope as their syntax or fixity declaration."
  UnknownNamesInPolarityPragmas_   -> "Names not declared in the same scope as their polarity pragmas."
  UselessAbstract_                 -> "`abstract' blocks where they have no effect."
  UselessInstance_                 -> "`instance' blocks where they have no effect."
  UselessPrivate_                  -> "`private' blocks where they have no effect."
  -- Scope and Type Checking Warning
  OldBuiltin_                      -> "Deprecated `BUILTIN' pragmas."
  EmptyRewritePragma_              -> "Empty `REWRITE' pragmas."
  UselessPublic_                   -> "`public' blocks where they have no effect."
  UselessInline_                   -> "`INLINE' pragmas where they have no effect."
  UnreachableClauses_              -> "Unreachable function clauses."
  GenericWarning_                  -> ""
  DeprecationWarning_              -> "Feature deprecation."
  InversionDepthReached_           -> "Inversions of pattern-matching failed due to exhausted inversion depth."
  TerminationIssue_                -> "Failed termination checks."
  CoverageIssue_                   -> "Failed coverage checks."
  CoverageNoExactSplit_            -> "Failed exact split checks."
  NotStrictlyPositive_             -> "Failed strict positivity checks."
  UnsolvedMetaVariables_           -> "Unsolved meta variables."
  UnsolvedInteractionMetas_        -> "Unsolved interaction meta variables."
  UnsolvedConstraints_             -> "Unsolved constraints."
  GenericNonFatalError_            -> ""
  SafeFlagPostulate_               -> "`postulate' blocks with the safe flag"
  SafeFlagPragma_                  -> "Unsafe `OPTIONS' pragmas with the safe flag."
  SafeFlagNonTerminating_          -> "`NON_TERMINATING' pragmas with the safe flag."
  SafeFlagTerminating_             -> "`TERMINATING' pragmas with the safe flag."
  SafeFlagPrimTrustMe_             -> "`primTrustMe' usages with the safe flag."
  SafeFlagNoPositivityCheck_       -> "`NO_POSITIVITY_CHECK' pragmas with the safe flag."
  SafeFlagPolarity_                -> "`POLARITY' pragmas with the safe flag."
  SafeFlagNoUniverseCheck_         -> "`NO_UNIVERSE_CHECK' pragmas with the safe flag."
  UserWarning_                     -> "User-defined warning added using the 'WARNING_ON_USAGE' pragma."
