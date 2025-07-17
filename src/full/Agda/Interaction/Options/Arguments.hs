-- | Definitions and tools for arguments of command-line options.

module Agda.Interaction.Options.Arguments where

import Data.Map (Map)
import Data.Map qualified as Map

import Agda.Interaction.Options.Help (allHelpTopics)
import Agda.Interaction.Options.ProfileOptions (validProfileOptionStrings)
import Agda.Interaction.Options.Warnings (warningNameToString, warningSets)
import Agda.Setup.EmacsMode qualified as EmacsMode (setupFlag, compileFlag, locateFlag)

-- * Names of the arguments of options that have a finite enumeration.

-- | Print the possible values of an argument of the given type.
optionValues :: Map String [String]
optionValues = Map.fromList $
  ( colorArg        , colorValues        ) :
  ( emacsModeArg    , emacsModeValues    ) :
  ( helpArg         , helpValues         ) :
  ( profileArg      , profileValues      ) :
  ( traceImportsArg , traceImportsValues ) :
  ( warningArg      , warningValues      ) :
  []

-- ** @--color@

-- | Argument to @--color@.
colorArg :: String
colorArg = "COLOR_MODE"

-- | Possible values for @--color@.
colorValues :: [String]
colorValues = [ "always", "auto", "never" ]

-- ** @--emacs-mode@

-- | Argument to @--emacs-mode@.
emacsModeArg :: String
emacsModeArg = "EMACS_MODE_COMMAND"

-- | Possible values for @--emacs-mode@.
emacsModeValues :: [String]
emacsModeValues = [EmacsMode.setupFlag, EmacsMode.compileFlag, EmacsMode.locateFlag]

-- ** @--help@

-- | Argument to @--help@.
helpArg :: String
helpArg = "HELP_TOPIC"

-- | Possible values for @--help@.
helpValues :: [String]
helpValues = map fst allHelpTopics

-- ** @--profile@

-- | Argument to @--profile@.
profileArg :: String
profileArg = "TO_PROFILE"

-- | Possible values for @--profile@.
profileValues :: [String]
profileValues = validProfileOptionStrings

-- ** @--trace-imports@

-- | Argument to @--trace-imports@.
traceImportsArg :: String
traceImportsArg = "IMPORT_TRACING_LEVEL"

-- | Possible values for @--trace-imports@.
traceImportsValues :: [String]
traceImportsValues = [ show n | n <- [0..3] ]

-- ** @--warning@

-- | Argument to @--warning@.
warningArg :: String
warningArg = "WARNING"

-- | Possible values for @--warning@.
warningValues :: [String]
warningValues = concat $
  map fst warningSets :
  map (\ w -> [w, "no" ++ w]) ws
  where
    ws = "error" : map warningNameToString [minBound..maxBound]
