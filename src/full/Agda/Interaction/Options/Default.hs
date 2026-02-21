-- | Default values for the options.

module Agda.Interaction.Options.Default where

import Agda.Interaction.Options.ProfileOptions () -- Null instance
import Agda.Interaction.Options.Types
import Agda.Interaction.Options.Warnings ( defaultWarningMode )
import Agda.Termination.CutOff           ( defaultCutOff )
import Agda.Utils.Null
import Agda.Utils.WithDefault

import Agda.Utils.Impossible

defaultOptions :: CommandLineOptions
defaultOptions = Options
  { optProgramName           = "agda"
  , optInputFile             = Nothing
  , optIncludePaths          = []
  , optAbsoluteIncludePaths  = []
  , optLibraries             = []
  , optOverrideLibrariesFile = Nothing
  , optDefaultLibs           = True
  , optUseLibs               = True
  , optTraceImports          = 1
  , optTrustedExecutables    = empty
  , optPrintAgdaDataDir      = False
  , optPrintAgdaAppDir       = False
  , optPrintOptions          = False
  , optPrintVersion          = Nothing
  , optPrintHelp             = Nothing
  , optBuildLibrary          = False
  , optSetup                 = False
  , optEmacsMode             = empty
  , optInteractive           = False
  , optGHCiInteraction       = False
  , optJSONInteraction       = False
  , optExitOnError           = False
  , optCompileDir            = Nothing
  , optGenerateVimFile       = False
  , optIgnoreInterfaces      = False
  , optIgnoreAllInterfaces   = False
  , optWriteInterfaces       = True
  , optPragmaOptions         = defaultPragmaOptions
  , optOnlyScopeChecking     = False
  , optTransliterate         = False
  , optDiagnosticsColour     = AutoColour
  , optMdOnlyAgdaBlocks      = False
  , optParallelChecking      = Sequential
  }

defaultPragmaOptions :: PragmaOptions
defaultPragmaOptions = PragmaOptions
  { _optShowImplicit               = Default
  , _optShowGeneralized            = Default
  , _optShowIrrelevant             = Default
  , _optUseUnicode                 = Default -- UnicodeOk
  , _optVerbose                    = empty
  , _optProfiling                  = empty
  , _optProp                       = Default
  , _optLevelUniverse              = Default
  , _optTwoLevel                   = Default
  , _optAllowUnsolved              = Default
  , _optAllowIncompleteMatch       = Default
  , _optPositivityCheck            = Default
  , _optTerminationCheck           = Default
  , _optTerminationDepth           = defaultCutOff
  , _optUniverseCheck              = Default
  , _optOmegaInOmega               = Default
  , _optCumulativity               = Default
  , _optSizedTypes                 = Default
  , _optGuardedness                = Default
  , _optInjectiveTypeConstructors  = Default
  , _optUniversePolymorphism       = Default
  , _optIrrelevantProjections      = Default
  , _optExperimentalIrrelevance    = Default
  , _optWithoutK                   = Default
  , _optCubicalCompatible          = Default
  , _optCopatterns                 = Default
  , _optPatternMatching            = Default
  , _optExactSplit                 = Default
  , _optHiddenArgumentPuns         = Default
  , _optEta                        = Default
  , _optForcing                    = Default
  , _optProjectionLike             = Default
  , _optErasure                    = Default
  , _optErasedMatches              = Default
  , _optEraseRecordParameters      = Default
  , _optRewriting                  = Default
  , _optLocalRewriting             = Default
  , _optCubical                    = Nothing
  , _optGuarded                    = Default
  , _optFirstOrder                 = Default
  , _optRequireUniqueMetaSolutions = Default
  , _optPostfixProjections         = Default
  , _optKeepPatternVariables       = Default
  , _optInferAbsurdClauses         = Default
  , _optInstanceSearchDepth        = 500
  , _optBacktrackingInstances      = Default
  , _optQualifiedInstances         = Default
  , _optInversionMaxDepth          = 50
  , _optSafe                       = Default
  , _optDoubleCheck                = Default
  , _optSyntacticEquality          = empty
  , _optWarningMode                = defaultWarningMode
  , _optCompileMain                = Default
  , _optCaching                    = Default
  , _optCountClusters              = Default
  , _optAutoInline                 = Default
  , _optPrintPatternSynonyms       = Default
  , _optFastReduce                 = Default
  , _optCallByName                 = Default
  , _optConfluenceCheck            = Nothing
  , _optCohesion                   = Default
  , _optFlatSplit                  = Default
  , _optPolarity                   = Default
  , _optOccurrence                 = Default
  , _optImportSorts                = Default
  , _optLoadPrimitives             = Default
  , _optAllowExec                  = Default
  , _optSaveMetas                  = Default
  , _optShowIdentitySubstitutions  = Default
  , _optKeepCoveringClauses        = Default
  , _optForcedArgumentRecursion    = Default
  , _optLargeIndices               = Default
  , _optExperimentalLazyInstances  = Default
  , _optQuoteMetas                 = Default
  }

-- Null instances

instance Null CommandLineOptions where
  empty = defaultOptions
  null = __IMPOSSIBLE__

instance Null PragmaOptions where
  empty = defaultPragmaOptions
