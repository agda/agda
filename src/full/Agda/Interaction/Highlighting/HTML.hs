{-# LANGUAGE CPP               #-}

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
import Control.Arrow ((***))
import Control.Monad
import Control.Monad.Trans

import Data.Function
import Data.Monoid
import Data.Foldable (toList, concatMap)
import Data.Maybe
import qualified Data.IntMap as IntMap
import qualified Data.Map    as Map
import qualified Data.List   as List
import Data.List.Split (splitWhen, chunksOf)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T

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

import Agda.Interaction.Highlighting.Generate
  (computeUnsolvedMetaWarnings, computeUnsolvedConstraints)

import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name (ModuleName)

import Agda.TypeChecking.Monad (TCM, useTC)
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
  pageGen ::
    FilePath -> C.TopLevelModuleName -> Text -> CompressedFile -> TCM ()
  pageGen dir mod contents hinfo = generatePage renderer dir mod
    where
    renderer :: FilePath -> Bool -> FilePath -> Text
    renderer css htmlHighlight _ =
      page css htmlHighlight mod $
      code htmlHighlight $ tokenStream contents hinfo

-- | Prepare information for HTML page generation.
--
--   The page generator receives the output directory as well as the
--   module's top level module name, its source code, and its
--   highlighting information.

generateHTMLWithPageGen
  :: (FilePath ->
      C.TopLevelModuleName -> Text -> CompressedFile -> TCM ())
     -- ^ Page generator.
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

      -- Pull source code and highlighting info from the state and
      -- generate all the web pages.
      mapM_ (\(n, mi) ->
              let i = TCM.miInterface mi in
              generatePage dir n
                (TCM.iSource i) (TCM.iHighlighting i)) .
        Map.toList =<< TCM.getVisitedModules

-- | Converts module names to the corresponding HTML file names.

modToFile :: C.TopLevelModuleName -> String -> FilePath
modToFile m ext =
  Network.URI.Encode.encode $
    render (pretty m) <.> ext

-- | Generates a highlighted, hyperlinked version of the given module.

generatePage
  :: (FilePath ->
      Bool -> FilePath -> Text)      -- ^ Page renderer.
  -> FilePath                        -- ^ Directory in which to create
                                     --   files.
  -> C.TopLevelModuleName            -- ^ Module to be highlighted.
  -> TCM ()
generatePage renderPage dir mod = do
  f   <- fromMaybe __IMPOSSIBLE__ . Map.lookup mod <$> useTC TCM.stModuleToSource
  css <- fromMaybe defaultCSSFile . optCSSFile <$> TCM.commandLineOptions
  pc  <- optHTMLOnlyCode <$> TCM.commandLineOptions
  ext <- optHTMLOutputExt <$> TCM.commandLineOptions
  let target = dir </> modToFile mod ext
  let html = renderPage css pc $ filePath f
  TCM.reportSLn "html" 1 $ "Generating HTML for " ++
                           render (pretty mod) ++
                           " (" ++ target ++ ")."
  liftIO $ UTF8.writeTextToFile target html


-- | Attach multiple Attributes

(!!) :: Html -> [Attribute] -> Html
h !! as = h ! mconcat as

-- | Constructs the web page, including headers.

page :: FilePath              -- ^ URL to the CSS file.
     -> Bool                  -- ^ Whether to reserve literate
     -> C.TopLevelModuleName  -- ^ Module to be highlighted.
     -> Html
     -> Text
page css htmlHighlight modName pageContent =
  renderHtml $ if htmlHighlight
  then pageContent
  else docTypeHtml $ hdr <> rest
  where

    hdr = Html5.head $ mconcat
      [ meta !! [ charset "utf-8" ]
      , Html5.title (toHtml $ render $ pretty modName)
      , link !! [ rel "stylesheet"
                , href $ stringValue css
                ]
      ]

    rest = body $ pre pageContent

-- | Constructs token stream ready to print.

tokenStream
     :: Text           -- ^ The contents of the module.
     -> CompressedFile -- ^ Highlighting information.
     -> [(Int, String, Aspects)]  -- ^ (position, contents, info)
tokenStream contents info =
  map (\cs -> case cs of
          (mi, (pos, _)) : _ ->
            (pos, map (snd . snd) cs, fromMaybe mempty mi)
          [] -> __IMPOSSIBLE__) $
  List.groupBy ((==) `on` fst) $
  map (\(pos, c) -> (IntMap.lookup pos infoMap, (pos, c))) $
  zip [1..] (T.unpack contents)
  where
  infoMap = toMap (decompress info)

-- | Constructs the HTML displaying the code.

code :: Bool          -- ^ Whether to generate non-code contents as-is
     -> [(Int, String, Aspects)]
     -> Html
code asIs = mconcat . if asIs
  then map mkMd . chunksOf 2 . splitWhen ((== Just Markup) . aspect . trd)
  else map mkHtml
  where
  trd (_, _, a) = a

  mkHtml :: (Int, String, Aspects) -> Html
  mkHtml (pos, s, mi) =
    -- Andreas, 2017-06-16, issue #2605:
    -- Do not create anchors for whitespace.
    applyUnless (mi == mempty) (annotate pos mi) $ toHtml s

  mkMd :: [[(Int, String, Aspects)]] -> Html
  mkMd = go
    where
      work a@(pos, s, mi) = case aspect mi of
        Just Background -> preEscapedToHtml s
        Just Markup     -> __IMPOSSIBLE__
        _               -> mkHtml a
      go [a, b] = mconcat [mconcat $ work <$> a, pre ! class_ "agda-code" $ mconcat $ work <$> b]
      go [a]    = mconcat $ work <$> a
      go _      = __IMPOSSIBLE__

  -- | Put anchors that enable referencing that token.
  --   We put a fail safe numeric anchor (file position) for internal references (issue #2756),
  --   as well as a heuristic name anchor for external references (issue #2604).
  annotate :: Int -> Aspects -> Html -> Html
  annotate pos mi = applyWhen hereAnchor (anchorage nameAttributes mempty <>) . anchorage posAttributes
    where
    -- | Warp an anchor (<A> tag) with the given attributes around some HTML.
    anchorage :: [Attribute] -> Html -> Html
    anchorage attrs html = a html !! attrs

    -- | File position anchor (unique, reliable).
    posAttributes :: [Attribute]
    posAttributes = concat
      [ [Attr.id $ stringValue $ show pos ]
      , toList $ fmap link $ definitionSite mi
      , class_ (stringValue $ unwords classes) <$ guard (not $ null classes)
      ]

    -- | Named anchor (not reliable, but useful in the general case for outside refs).
    nameAttributes :: [Attribute]
    nameAttributes = [ Attr.id $ stringValue $ fromMaybe __IMPOSSIBLE__ $ mDefSiteAnchor ]

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

    -- | Should we output a named anchor?
    --   Only if we are at the definition site now (@here@)
    --   and such a pretty named anchor exists (see 'defSiteAnchor').
    hereAnchor      :: Bool
    hereAnchor      = here && isJust mDefSiteAnchor

    mDefinitionSite :: Maybe DefinitionSite
    mDefinitionSite = definitionSite mi

    -- | Are we at the definition site now?
    here            :: Bool
    here            = maybe False defSiteHere mDefinitionSite

    mDefSiteAnchor  :: Maybe String
    mDefSiteAnchor  = maybe __IMPOSSIBLE__ defSiteAnchor mDefinitionSite

    link (DefinitionSite m pos _here _aName) = href $ stringValue $
      -- If the definition site points to the top of a file,
      -- we drop the anchor part and just link to the file.
      applyUnless (pos <= 1)
        (++ "#" ++
         Network.URI.Encode.encode (show pos))
         -- Network.URI.Encode.encode (fromMaybe (show pos) aName)) -- Named links disabled
        (Network.URI.Encode.encode $ modToFile m "html")
