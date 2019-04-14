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

import Agda.Interaction.Options
import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.Highlighting.Common

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

-- | The directive inserted before the rendered code blocks

rstDelimiter :: String
rstDelimiter = ".. raw:: html\n"

-- | Determine how to highlight the file

highlightOnlyCode :: HtmlHighlight -> FileType -> Bool
highlightOnlyCode HighlightAll  _ = False
highlightOnlyCode HighlightCode _ = True
highlightOnlyCode HighlightAuto AgdaFileType = False
highlightOnlyCode HighlightAuto MdFileType   = True
highlightOnlyCode HighlightAuto RstFileType  = True
highlightOnlyCode HighlightAuto OrgFileType  = True
highlightOnlyCode HighlightAuto TexFileType  = False

-- | Determine the generated file extension

highlightedFileExt :: HtmlHighlight -> FileType -> String
highlightedFileExt hh ft
  | not $ highlightOnlyCode hh ft = "html"
  | otherwise = case ft of
      AgdaFileType -> "html"
      MdFileType   -> "md"
      RstFileType  -> "rst"
      TexFileType  -> "tex"
      OrgFileType  -> "org"

-- | Generates HTML files from all the sources which have been
--   visited during the type checking phase.
--
--   This function should only be called after type checking has
--   completed successfully.

type PageGen = FilePath    -- ^ Output directory
  -> FileType              -- ^ Source file type
  -> Bool                  -- ^ Return value of `highlightOnlyCode`
  -> String                -- ^ Output file extension (return
                           --   value of `highlightedFileExt`)
  -> C.TopLevelModuleName
  -> Text
  -> CompressedFile        -- ^ Highlighting information
  -> TCM ()

generateHTML :: TCM ()
generateHTML = generateHTMLWithPageGen pageGen
  where
  pageGen :: PageGen
  pageGen dir ft pc ext mod contents hinfo =
    generatePage (renderer pc ft) ext dir mod
    where
    renderer :: Bool -> FileType -> FilePath -> FilePath -> Text
    renderer onlyCode fileType css _ =
      page css onlyCode mod $
      code onlyCode fileType $
      tokenStream contents hinfo

-- | Prepare information for HTML page generation.
--
--   The page generator receives the output directory as well as the
--   module's top level module name, its source code, and its
--   highlighting information.

generateHTMLWithPageGen
  :: PageGen
     -- ^ Page generator.
  -> TCM ()
generateHTMLWithPageGen generatePage = do
      options <- TCM.commandLineOptions

      -- There is a default directory given by 'defaultHTMLDir'
      let dir = optHTMLDir options
      let htmlHighlight = optHTMLHighlight options
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
              let i  = TCM.miInterface mi
                  ft = TCM.iFileType i in
              generatePage dir ft
                (highlightOnlyCode htmlHighlight ft)
                (highlightedFileExt htmlHighlight ft) n
                (TCM.iSource i) (TCM.iHighlighting i)) .
        Map.toList =<< TCM.getVisitedModules

-- | Converts module names to the corresponding HTML file names.

modToFile :: C.TopLevelModuleName -> String -> FilePath
modToFile m ext =
  Network.URI.Encode.encode $
    render (pretty m) <.> ext

-- | Generates a highlighted, hyperlinked version of the given module.

generatePage
  :: (FilePath -> FilePath -> Text)  -- ^ Page renderer.
  -> String                          -- ^ Output file extension.
  -> FilePath                        -- ^ Directory in which to create
                                     --   files.
  -> C.TopLevelModuleName            -- ^ Module to be highlighted.
  -> TCM ()
generatePage renderPage ext dir mod = do
  f   <- fromMaybe __IMPOSSIBLE__ . Map.lookup mod <$> useTC TCM.stModuleToSource
  css <- fromMaybe defaultCSSFile . optCSSFile <$> TCM.commandLineOptions
  let target = dir </> modToFile mod ext
  let html = renderPage css $ filePath f
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

    rest = body $ (pre ! class_ "Agda") pageContent

-- | Position, Contents, Infomation

type TokenInfo =
  ( Int
  , String
  , Aspects
  )

-- | Constructs token stream ready to print.

tokenStream
     :: Text           -- ^ The contents of the module.
     -> CompressedFile -- ^ Highlighting information.
     -> [TokenInfo]
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

code :: Bool     -- ^ Whether to generate non-code contents as-is
     -> FileType -- ^ Source file type
     -> [TokenInfo]
     -> Html
code onlyCode fileType = mconcat . if onlyCode
  then case fileType of
         -- Explicitly written all cases, so people
         -- get compile error when adding new file types
         -- when they forget to modify the code here
         RstFileType  -> map mkRst . splitByMarkup
         MdFileType   -> map mkMd . chunksOf 2 . splitByMarkup
         AgdaFileType -> map mkHtml
         -- Any points for using this option?
         TexFileType  -> map mkMd . chunksOf 2 . splitByMarkup
         OrgFileType  -> map mkOrg . splitByMarkup
  else map mkHtml
  where
  trd (_, _, a) = a

  splitByMarkup :: [TokenInfo] -> [[TokenInfo]]
  splitByMarkup = splitWhen $ (== Just Markup) . aspect . trd

  mkHtml :: TokenInfo -> Html
  mkHtml (pos, s, mi) =
    -- Andreas, 2017-06-16, issue #2605:
    -- Do not create anchors for whitespace.
    applyUnless (mi == mempty) (annotate pos mi) $ toHtml s

  -- | Proposed in #3373, implemented in #3384
  mkRst :: [TokenInfo] -> Html
  mkRst = mconcat . (toHtml rstDelimiter :) . map go
    where
      go token@(_, s, mi) = if aspect mi == Just Background
        then preEscapedToHtml s
        else mkHtml token

  -- | Proposed in #3137, implemented in #3313
  --   Improvement proposed in #3366, implemented in #3367
  mkMd :: [[TokenInfo]] -> Html
  mkMd = mconcat . go
    where
      work token@(_, s, mi) = case aspect mi of
        Just Background -> preEscapedToHtml s
        Just Markup     -> __IMPOSSIBLE__
        _               -> mkHtml token
      go [a, b] = [ mconcat $ work <$> a
                  , pre ! class_ "Agda" $ mconcat $ work <$> b
                  ]
      go [a]    = work <$> a
      go _      = __IMPOSSIBLE__

  mkOrg :: [TokenInfo] -> Html
  mkOrg = mconcat . map go
    where
      go token@(_, s, mi) = if aspect mi == Just Background
        then preEscapedToHtml s
        else mkHtml token

  -- | Put anchors that enable referencing that token.
  --   We put a fail safe numeric anchor (file position) for internal references
  --   (issue #2756), as well as a heuristic name anchor for external references
  --   (issue #2604).
  annotate :: Int -> Aspects -> Html -> Html
  annotate pos mi = applyWhen hereAnchor
      (anchorage nameAttributes mempty <>) . anchorage posAttributes
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
      , otherAspectClasses (toList $ otherAspects mi)
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
