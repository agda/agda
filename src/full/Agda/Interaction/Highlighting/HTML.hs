-- | Function for generating highlighted, hyperlinked HTML from Agda
-- sources.

module Agda.Interaction.Highlighting.HTML
  ( generateHTML
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Arrow ((***))
import System.FilePath
import System.Directory
import Text.XHtml.Strict
import Data.Function
import Data.Monoid
import Data.Maybe
import qualified Data.Map  as Map
import qualified Data.List as List
import qualified Agda.Utils.IO as UTF8

import Paths_Agda

import Agda.Interaction.Highlighting.Generate
import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.Highlighting.Range
import qualified Agda.Interaction.Imports as Imp
import Agda.TypeChecking.Monad (TCM)
import qualified Agda.TypeChecking.Monad as TCM
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common
import qualified Agda.Syntax.Scope.Monad as Scope
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Interaction.Options

-- | The name of the default CSS file.

defaultCSSFile :: FilePath
defaultCSSFile = "Agda.css"

-- | Generates HTML files from all the sources which the given module
-- depends on (including the module itself).
--
-- This function should only be called after type checking has
-- completed successfully.

generateHTML :: A.ModuleName -> TCM ()
generateHTML mod = do
  options <- TCM.commandLineOptions
  case optHTMLDir options of
    Nothing  -> TCM.typeError TCM.HTMLDirUndefined
    Just dir -> do
      liftIO $ createDirectoryIfMissing True dir

      -- If the default CSS file should be used, then it is copied to
      -- the output directory.
      liftIO $ when (isNothing $ optCSSFile options) $ do
        cssFile <- getDataFileName defaultCSSFile
        copyFile cssFile (dir </> defaultCSSFile)

      TCM.reportSLn "html" 1 $
        "\nWarning: HTML is currently generated for ALL files which can be\n\
        \reached from the given module, including library files.\n"

      -- Pull highlighting info from the state and generate all the
      -- web pages.
      mapM_ (\(m, h) -> generatePage dir m h) =<<
        map (id *** TCM.iHighlighting) . Map.toList <$>
          TCM.getAllModules

-- | Converts module names to the corresponding HTML file names.

modToFile :: [String] -> FilePath
modToFile m = List.intercalate "." m <.> "html"

-- | Generates an HTML file with a highlighted, hyperlinked version of
-- the given module.

generatePage
  :: FilePath         -- ^ Directory in which to create files.
  -> A.ModuleName     -- ^ Module to be highlighted.
  -> HighlightingInfo -- ^ Syntax highlighting info for the module.
  -> TCM ()
generatePage dir mod highlighting = do
  contents <- liftIO $ UTF8.readTextFile (source highlighting)
  css      <- maybe defaultCSSFile id . optCSSFile <$>
                TCM.commandLineOptions
  let html = page css mod contents (info highlighting)
  TCM.reportSLn "html" 1 $ "Generating HTML for " ++ show mod ++
                           " (" ++ target ++ ")."
  liftIO $ UTF8.writeFile target (renderHtml html)
  where target = dir </> modToFile (map show $ A.mnameToList mod)

-- | Constructs the web page, including headers.

page :: FilePath       -- ^ URL to the CSS file.
     -> A.ModuleName   -- ^ Module to be highlighted.
     -> String         -- ^ The contents of the module.
     -> CompressedFile -- ^ Highlighting information.
     -> Html
page css modName contents info =
  header (thetitle << show modName
            +++
          meta ! [ httpequiv "Content-Type"
                 , content "text/html; charset=UTF-8"
                 ]
            +++
          meta ! [ httpequiv "Content-Style-Type"
                 , content "text/css"
                 ]
            +++
          thelink noHtml ! [ href css
                           , rel "stylesheet"
                           , thetype "text/css"
                           ])
  +++
  body << pre << code modName contents info

-- | Constructs the HTML displaying the code.

code :: A.ModuleName   -- ^ Module to be highlighted.
     -> String         -- ^ The contents of the module.
     -> CompressedFile -- ^ Highlighting information.
     -> Html
code modName contents info =
  mconcat $
  map (\(pos, s, mi) -> annotate pos mi (stringToHtml s)) $
  map (\cs@((mi, (pos, _)) : _) ->
         (pos, map (snd . snd) cs, maybe mempty id mi)) $
  List.groupBy ((==) `on` fst) $
  map (\(pos, c) -> (Map.lookup pos infoMap, (pos, c))) $
  zip [1..] contents
  where
  infoMap = toMap (decompress info)

  annotate :: Integer -> MetaInfo -> Html -> Html
  annotate pos mi = anchor ! attributes
    where
    attributes =
      [name (show pos)] ++
      maybe [] link (definitionSite mi) ++
      (case classes of
        [] -> []
        cs -> [theclass $ unwords cs])

    classes =
      maybe [] noteClasses (note mi)
      ++ otherAspectClasses (otherAspects mi)
      ++ maybe [] aspectClasses (aspect mi)
      ++ maybe [] linkClasses (definitionSite mi)

    aspectClasses (Name mKind op) = kindClass ++ opClass
      where
      kindClass = maybe [] ((: []) . showKind) mKind

      showKind (Constructor Inductive)   = "InductiveConstructor"
      showKind (Constructor CoInductive) = "CoinductiveConstructor"
      showKind k                         = show k

      opClass = if op then ["Operator"] else []
    aspectClasses a = [show a]

    otherAspectClasses = map show

    -- Notes are not included.
    noteClasses s = []

    link (m, f, pos) = [href $ modToFile m ++ "#" ++ show pos]
    linkClasses (m, f, pos)
      | m == map show (A.mnameToList modName) = ["InternalLink"]
      | otherwise                             = ["ExternalLink"]
