{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Function for generating highlighted, hyperlinked HTML from Agda
-- sources.

module Agda.Interaction.Highlighting.HTML
  ( generateHTML
  -- Reused by PandocAgda
  , defaultCSSFile
  , generateHTMLWithPageGen
  , generatePage
  , page
  , tokenStream
  , code
  ) where

import Prelude hiding ((!!), concatMap)
import Control.Monad
import Control.Monad.Trans

import Data.Function
import Data.Monoid
import Data.Foldable (toList, concatMap)
import Data.Maybe
import qualified Data.IntMap as IntMap
import qualified Data.Map    as Map
import qualified Data.List   as List
import Data.Text.Lazy (Text)

import qualified Network.URI.Encode

import System.FilePath
import System.Directory

import Text.Blaze.Html5 hiding (code, map, title)
import qualified Text.Blaze.Html5 as Html5
import Text.Blaze.Html5.Attributes as Attr
import Text.Blaze.Html.Renderer.Text
  -- The imported operator (!) attaches an Attribute to an Html value
  -- The defined operator (!!) attaches a list of such Attributes

import Paths_Agda

import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.Options

import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Common

import Agda.TypeChecking.Monad (TCM)
import qualified Agda.TypeChecking.Monad as TCM

import Agda.Utils.FileName (filePath)
import Agda.Utils.Function
import Agda.Utils.Lens
import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.Pretty hiding ((<>))
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

-- | The name of the default CSS file.

defaultCSSFile :: FilePath
defaultCSSFile = "Agda.css"

-- | Generates HTML files from all the sources which have been
--   visited during the type checking phase.
--
--   This function should only be called after type checking has
--   completed successfully.

generateHTML :: TCM ()
generateHTML = generateHTMLWithPageGen pageGen
  where
  pageGen :: FilePath -> C.TopLevelModuleName -> CompressedFile -> TCM ()
  pageGen dir mod hinfo = generatePage renderer dir mod
    where
    renderer :: FilePath -> FilePath -> String -> Text
    renderer css _ contents = page css mod $ code $ tokenStream contents hinfo

-- | Prepare information for HTML page generation.
--
--   The page generator receives the file path of the module,
--   the top level module name of the module
--   and the highlighting information of the module.

generateHTMLWithPageGen
  :: (FilePath -> C.TopLevelModuleName -> CompressedFile -> TCM ())  -- ^ Page generator
  -> TCM ()
generateHTMLWithPageGen generatePage = do
      options <- TCM.commandLineOptions

      -- There is a default directory given by 'defaultHTMLDir'
      let dir = optHTMLDir options
      liftIO $ createDirectoryIfMissing True dir

      -- If the default CSS file should be used, then it is copied to
      -- the output directory.
      liftIO $ when (isNothing $ optCSSFile options) $ do
        cssFile <- getDataFileName defaultCSSFile
        copyFile cssFile (dir </> defaultCSSFile)

      TCM.reportSLn "html" 1 $ unlines
        [ ""
        , "Warning: HTML is currently generated for ALL files which can be"
        , "reached from the given module, including library files."
        ]

      -- Pull highlighting info from the state and generate all the
      -- web pages.
      mapM_ (\(m, h) -> generatePage dir m h) =<<
        map (mapSnd $ TCM.iHighlighting . TCM.miInterface) .
          Map.toList <$> TCM.getVisitedModules

-- | Converts module names to the corresponding HTML file names.

modToFile :: C.TopLevelModuleName -> FilePath
modToFile m =
  Network.URI.Encode.encode $
    render (pretty m) <.> "html"

-- | Generates a highlighted, hyperlinked version of the given module.

generatePage
  :: (FilePath -> FilePath -> String -> Text)  -- ^ Page renderer
  -> FilePath              -- ^ Directory in which to create files.
  -> C.TopLevelModuleName  -- ^ Module to be highlighted.
  -> TCM ()
generatePage renderpage dir mod = do
  f <- fromMaybe __IMPOSSIBLE__ . Map.lookup mod <$> use TCM.stModuleToSource
  contents <- liftIO $ UTF8.readTextFile $ filePath f
  css      <- fromMaybe defaultCSSFile . optCSSFile <$>
                TCM.commandLineOptions
  let html = renderpage css (filePath f) contents
  TCM.reportSLn "html" 1 $ "Generating HTML for " ++
                           render (pretty mod) ++
                           " (" ++ target ++ ")."
  liftIO $ UTF8.writeTextToFile target html
  where target = dir </> modToFile mod


-- | Attach multiple Attributes

(!!) :: Html -> [Attribute] -> Html
h !! as = h ! mconcat as

-- | Constructs the web page, including headers.

page :: FilePath              -- ^ URL to the CSS file.
     -> C.TopLevelModuleName  -- ^ Module to be highlighted.
     -> Html
     -> Text
page css modName pagecontent = renderHtml $ docTypeHtml $ hdr <> rest

  where

    hdr = Html5.head $ mconcat
      [ meta !! [ charset "utf-8" ]
      , Html5.title (toHtml $ render $ pretty modName)
      , link !! [ rel "stylesheet"
                , href (stringValue css)
                ]
      ]

    rest = body (pre pagecontent)

-- | Constructs token stream ready to print.

tokenStream
     :: String         -- ^ The contents of the module.
     -> CompressedFile -- ^ Highlighting information.
     -> [(Int, String, Aspects)]  -- ^ (position, contents, info)
tokenStream contents info =
  map (\cs -> case cs of
          (mi, (pos, _)) : _ ->
            (pos, map (snd . snd) cs, fromMaybe mempty mi)
          [] -> __IMPOSSIBLE__) $
  List.groupBy ((==) `on` fst) $
  map (\(pos, c) -> (IntMap.lookup pos infoMap, (pos, c))) $
  zip [1..] contents
  where
  infoMap = toMap (decompress info)

-- | Constructs the HTML displaying the code.

code :: [(Int, String, Aspects)]
     -> Html
code = mconcat . map mkHtml
  where
  mkHtml :: (Int, String, Aspects) -> Html
  mkHtml (pos, s, mi) =
    -- Andreas, 2017-06-16, issue #2605:
    -- Do not create anchors for whitespace.
    applyUnless (mi == mempty) (annotate pos mi) $ toHtml s

  annotate :: Int -> Aspects -> Html -> Html
  annotate pos mi content = a content !! attributes
    where
    attributes = concat
      [ [Attr.id $ stringValue $ show pos ]
      , toList $ fmap link $ definitionSite mi
      , class_ (stringValue $ unwords classes) <$ guard (not $ null classes)
      ]

    classes = concat
      [ concatMap noteClasses (note mi)
      , otherAspectClasses (otherAspects mi)
      , concatMap aspectClasses (aspect mi)
      ]

    aspectClasses (Name mKind op) = kindClass ++ opClass
      where
      kindClass = toList $ fmap showKind mKind

      showKind (Constructor Inductive)   = "InductiveConstructor"
      showKind (Constructor CoInductive) = "CoinductiveConstructor"
      showKind k                         = show k

      opClass = if op then ["Operator"] else []
    aspectClasses a = [show a]

    otherAspectClasses = map show

    -- Notes are not included.
    noteClasses s = []

    link (DefinitionSite m pos _ _) = href $ stringValue $
      -- If the definition site points to the top of a file,
      -- we drop the anchor part and just link to the file.
      applyUnless (pos <= 1)
        (++ "#" ++
         Network.URI.Encode.encode (show pos))
        (Network.URI.Encode.encode $ modToFile m)
