
-- | Backend for generating highlighted, hyperlinked HTML from Agda sources.

module Agda.Interaction.Highlighting.HTML.Backend
  ( htmlBackend
  ) where

import Agda.Interaction.Highlighting.HTML.Base

import Prelude hiding ((!!), concatMap)

import Control.DeepSeq
import Control.Monad.Trans ( MonadIO )
import Control.Monad.Except ( MonadError(throwError) )

import Data.Map (Map)

import GHC.Generics (Generic)

import Agda.Interaction.Options
    ( ArgDescr(ReqArg, NoArg)
    , OptDescr(..)
    , Flag
    )
import Agda.Compiler.Backend (Backend(..), Backend'(..), Recompile(..))
import Agda.Compiler.Common (IsMain(..), curIF)

import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)

import Agda.TypeChecking.Monad
  ( MonadDebug
  , ReadTCState
  , Definition
  , reportS
  )

-- | Options for HTML generation

data HtmlFlags = HtmlFlags
  { htmlFlagEnabled              :: Bool
  , htmlFlagDir                  :: FilePath
  , htmlFlagHighlight            :: HtmlHighlight
  , htmlFlagHighlightOccurrences :: Bool
  , htmlFlagCssFile              :: Maybe FilePath
  } deriving (Eq, Generic)

instance NFData HtmlFlags

data HtmlCompileEnv = HtmlCompileEnv
  { htmlCompileEnvOpts :: HtmlOptions
  }

data HtmlModuleEnv = HtmlModuleEnv
  { htmlModEnvCompileEnv :: HtmlCompileEnv
  , htmlModEnvName       :: TopLevelModuleName
  }

data HtmlModule = HtmlModule
data HtmlDef = HtmlDef

htmlBackend :: Backend
htmlBackend = Backend htmlBackend'

htmlBackend' :: Backend' HtmlFlags HtmlCompileEnv HtmlModuleEnv HtmlModule HtmlDef
htmlBackend' = Backend'
  { backendName           = "HTML"
  , backendVersion        = Nothing
  , options               = initialHtmlFlags
  , commandLineFlags      = htmlFlags
  , isEnabled             = htmlFlagEnabled
  , preCompile            = preCompileHtml
  , preModule             = preModuleHtml
  , compileDef            = compileDefHtml
  , postModule            = postModuleHtml
  , postCompile           = postCompileHtml
  -- --only-scope-checking works, but with the caveat that cross-module links
  -- will not have their definition site populated.
  , scopeCheckingSuffices = True
  , mayEraseType          = const $ return False
  }

initialHtmlFlags :: HtmlFlags
initialHtmlFlags = HtmlFlags
  { htmlFlagEnabled   = False
  , htmlFlagDir       = defaultHTMLDir
  , htmlFlagHighlight = HighlightAll
  -- Don't enable by default because it causes potential
  -- performance problems
  , htmlFlagHighlightOccurrences = False
  , htmlFlagCssFile              = Nothing
  }

htmlOptsOfFlags :: HtmlFlags -> HtmlOptions
htmlOptsOfFlags flags = HtmlOptions
  { htmlOptDir = htmlFlagDir flags
  , htmlOptHighlight = htmlFlagHighlight flags
  , htmlOptHighlightOccurrences = htmlFlagHighlightOccurrences flags
  , htmlOptCssFile = htmlFlagCssFile flags
  }

-- | The default output directory for HTML.

defaultHTMLDir :: FilePath
defaultHTMLDir = "html"

htmlFlags :: [OptDescr (Flag HtmlFlags)]
htmlFlags =
    [ Option []     ["html"] (NoArg htmlFlag)
                    "generate HTML files with highlighted source code"
    , Option []     ["html-dir"] (ReqArg htmlDirFlag "DIR")
                    ("directory in which HTML files are placed (default: " ++
                     defaultHTMLDir ++ ")")
    , Option []     ["highlight-occurrences"] (NoArg highlightOccurrencesFlag)
                    ("highlight all occurrences of hovered symbol in generated " ++
                     "HTML files")
    , Option []     ["css"] (ReqArg cssFlag "URL")
                    "the CSS file used by the HTML files (can be relative)"
    , Option []     ["html-highlight"] (ReqArg htmlHighlightFlag "[code,all,auto]")
                    ("whether to highlight only the code parts (code) or " ++
                     "the file as a whole (all) or " ++
                     "decide by source file type (auto)")
    ]

htmlFlag :: Flag HtmlFlags
htmlFlag o = return $ o { htmlFlagEnabled = True }

htmlDirFlag :: FilePath -> Flag HtmlFlags
htmlDirFlag d o = return $ o { htmlFlagDir = d }

cssFlag :: FilePath -> Flag HtmlFlags
cssFlag f o = return $ o { htmlFlagCssFile = Just f }

highlightOccurrencesFlag :: Flag HtmlFlags
highlightOccurrencesFlag o = return $ o { htmlFlagHighlightOccurrences = True }

parseHtmlHighlightFlag :: MonadError String m => String -> m HtmlHighlight
parseHtmlHighlightFlag "code" = return HighlightCode
parseHtmlHighlightFlag "all"  = return HighlightAll
parseHtmlHighlightFlag "auto" = return HighlightAuto
parseHtmlHighlightFlag opt    = throwError $ concat ["Invalid option <", opt, ">, expected <all>, <auto> or <code>"]

htmlHighlightFlag :: String -> Flag HtmlFlags
htmlHighlightFlag opt    o = do
  flag <- parseHtmlHighlightFlag opt
  return $ o { htmlFlagHighlight = flag }

runLogHtmlWithMonadDebug :: MonadDebug m => LogHtmlT m a -> m a
runLogHtmlWithMonadDebug = runLogHtmlWith $ reportS "html" 1

preCompileHtml
  :: (MonadIO m, MonadDebug m)
  => HtmlFlags
  -> m HtmlCompileEnv
preCompileHtml flags = runLogHtmlWithMonadDebug $ do
  logHtml $ unlines
    [ "Warning: HTML is currently generated for ALL files which can be"
    , "reached from the given module, including library files."
    ]
  let opts = htmlOptsOfFlags flags
  prepareCommonDestinationAssets opts
  return $ HtmlCompileEnv opts

preModuleHtml
  :: Applicative m
  => HtmlCompileEnv
  -> IsMain
  -> TopLevelModuleName
  -> Maybe FilePath
  -> m (Recompile HtmlModuleEnv HtmlModule)
preModuleHtml cenv _isMain modName _ifacePath = pure $ Recompile (HtmlModuleEnv cenv modName)

compileDefHtml
  :: Applicative m
  => HtmlCompileEnv
  -> HtmlModuleEnv
  -> IsMain
  -> Definition
  -> m HtmlDef
compileDefHtml _env _menv _isMain _def = pure HtmlDef

postModuleHtml
  :: (MonadIO m, MonadDebug m, ReadTCState m)
  => HtmlCompileEnv
  -> HtmlModuleEnv
  -> IsMain
  -> TopLevelModuleName
  -> [HtmlDef]
  -> m HtmlModule
postModuleHtml _env menv _isMain _modName _defs = do
  let generatePage = defaultPageGen . htmlCompileEnvOpts . htmlModEnvCompileEnv $ menv
  htmlSrc <- srcFileOfInterface (htmlModEnvName menv) <$> curIF
  runLogHtmlWithMonadDebug $ generatePage htmlSrc
  return HtmlModule

postCompileHtml
  :: Applicative m
  => HtmlCompileEnv
  -> IsMain
  -> Map TopLevelModuleName HtmlModule
  -> m ()
postCompileHtml _cenv _isMain _modulesByName = pure ()
