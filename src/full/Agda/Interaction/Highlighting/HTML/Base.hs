
-- | Function for generating highlighted, hyperlinked HTML from Agda
-- sources.

module Agda.Interaction.Highlighting.HTML.Base
  ( HtmlOptions(..)
  , HtmlHighlight(..)
  , prepareCommonDestinationAssets
  , srcFileOfInterface
  , defaultPageGen
  , MonadLogHtml(logHtml)
  , LogHtmlT
  , runLogHtmlWith
  ) where

import Prelude hiding ((!!), concatMap)

import Control.DeepSeq
import Control.Monad
import Control.Monad.Trans ( MonadIO(..), lift )
import Control.Monad.Trans.Reader ( ReaderT(runReaderT), ask )

import Data.Function ( on )
import Data.Foldable (toList, concatMap)
import Data.Maybe
import qualified Data.IntMap as IntMap
import qualified Data.List   as List
import Data.List.Split (splitWhen, chunksOf)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T

import GHC.Generics (Generic)

import qualified Network.URI.Encode

import System.FilePath
import System.Directory

import Text.Blaze.Html5
    ( preEscapedToHtml
    , toHtml
    , stringValue
    , Html
    , (!)
    , Attribute
    )
import qualified Text.Blaze.Html5 as Html5
import qualified Text.Blaze.Html5.Attributes as Attr
import Text.Blaze.Html.Renderer.Text ( renderHtml )
  -- The imported operator (!) attaches an Attribute to an Html value
  -- The defined operator (!!) attaches a list of such Attributes

import Paths_Agda

import Agda.Interaction.Highlighting.Precise hiding (toList)

import Agda.Syntax.Common
import Agda.Syntax.TopLevelModuleName

import qualified Agda.TypeChecking.Monad as TCM
  ( Interface(..)
  )

import Agda.Utils.Function
import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.Pretty

import Agda.Utils.Impossible

-- | The Agda data directory containing the files for the HTML backend.

htmlDataDir :: FilePath
htmlDataDir = "html"

-- | The name of the default CSS file.

defaultCSSFile :: FilePath
defaultCSSFile = "Agda.css"

-- | The name of the occurrence-highlighting JS file.

occurrenceHighlightJsFile :: FilePath
occurrenceHighlightJsFile = "highlight-hover.js"

-- | The directive inserted before the rendered code blocks

rstDelimiter :: String
rstDelimiter = ".. raw:: html\n"

-- | The directive inserted before rendered code blocks in org

orgDelimiterStart :: String
orgDelimiterStart = "#+BEGIN_EXPORT html\n<pre class=\"Agda\">\n"

-- | The directive inserted after rendered code blocks in org

orgDelimiterEnd :: String
orgDelimiterEnd = "</pre>\n#+END_EXPORT\n"

-- | Determine how to highlight the file

data HtmlHighlight = HighlightAll | HighlightCode | HighlightAuto
  deriving (Show, Eq, Generic)

instance NFData HtmlHighlight

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

-- | Options for HTML generation

data HtmlOptions = HtmlOptions
  { htmlOptDir                  :: FilePath
  , htmlOptHighlight            :: HtmlHighlight
  , htmlOptHighlightOccurrences :: Bool
  , htmlOptCssFile              :: Maybe FilePath
  } deriving Eq

-- | Internal type bundling the information related to a module source file

data HtmlInputSourceFile = HtmlInputSourceFile
  { _srcFileModuleName :: TopLevelModuleName
  , _srcFileType :: FileType
  -- ^ Source file type
  , _srcFileText :: Text
  -- ^ Source text
  , _srcFileHighlightInfo :: HighlightingInfo
  -- ^ Highlighting info
  }

-- | Bundle up the highlighting info for a source file

srcFileOfInterface ::
  TopLevelModuleName -> TCM.Interface -> HtmlInputSourceFile
srcFileOfInterface m i = HtmlInputSourceFile m (TCM.iFileType i) (TCM.iSource i) (TCM.iHighlighting i)

-- | Logging during HTML generation

type HtmlLogMessage = String
type HtmlLogAction m = HtmlLogMessage -> m ()

class MonadLogHtml m where
  logHtml :: HtmlLogAction m

type LogHtmlT m = ReaderT (HtmlLogAction m) m

instance Monad m => MonadLogHtml (LogHtmlT m) where
  logHtml message = do
    doLog <- ask
    lift $ doLog message

runLogHtmlWith :: Monad m => HtmlLogAction m -> LogHtmlT m a -> m a
runLogHtmlWith = flip runReaderT

renderSourceFile :: HtmlOptions -> HtmlInputSourceFile -> Text
renderSourceFile opts = renderSourcePage
  where
  cssFile = fromMaybe defaultCSSFile (htmlOptCssFile opts)
  highlightOccur = htmlOptHighlightOccurrences opts
  htmlHighlight = htmlOptHighlight opts
  renderSourcePage (HtmlInputSourceFile moduleName fileType sourceCode hinfo) =
    page cssFile highlightOccur onlyCode moduleName pageContents
    where
      tokens = tokenStream sourceCode hinfo
      onlyCode = highlightOnlyCode htmlHighlight fileType
      pageContents = code onlyCode fileType tokens

defaultPageGen :: (MonadIO m, MonadLogHtml m) => HtmlOptions -> HtmlInputSourceFile -> m ()
defaultPageGen opts srcFile@(HtmlInputSourceFile moduleName ft _ _) = do
  logHtml $ render $ "Generating HTML for"  <+> pretty moduleName <+> ((parens (pretty target)) <> ".")
  writeRenderedHtml html target
  where
    ext = highlightedFileExt (htmlOptHighlight opts) ft
    target = (htmlOptDir opts) </> modToFile moduleName ext
    html = renderSourceFile opts srcFile

prepareCommonDestinationAssets :: MonadIO m => HtmlOptions -> m ()
prepareCommonDestinationAssets options = liftIO $ do
  -- There is a default directory given by 'defaultHTMLDir'
  let htmlDir = htmlOptDir options
  createDirectoryIfMissing True htmlDir

  -- If the default CSS file should be used, then it is copied to
  -- the output directory.
  let cssFile = htmlOptCssFile options
  when (isNothing $ cssFile) $ do
    defCssFile <- getDataFileName $
      htmlDataDir </> defaultCSSFile
    copyFile defCssFile (htmlDir </> defaultCSSFile)

  let highlightOccurrences = htmlOptHighlightOccurrences options
  when highlightOccurrences $ do
    highlightJsFile <- getDataFileName $
      htmlDataDir </> occurrenceHighlightJsFile
    copyFile highlightJsFile (htmlDir </> occurrenceHighlightJsFile)

-- | Converts module names to the corresponding HTML file names.

modToFile :: TopLevelModuleName -> String -> FilePath
modToFile m ext = Network.URI.Encode.encode $ render (pretty m) <.> ext

-- | Generates a highlighted, hyperlinked version of the given module.

writeRenderedHtml
  :: MonadIO m
  => Text       -- ^ Rendered page
  -> FilePath   -- ^ Output path.
  -> m ()
writeRenderedHtml html target = liftIO $ UTF8.writeTextToFile target html


-- | Attach multiple Attributes

(!!) :: Html -> [Attribute] -> Html
h !! as = h ! mconcat as

-- | Constructs the web page, including headers.

page :: FilePath              -- ^ URL to the CSS file.
     -> Bool                  -- ^ Highlight occurrences
     -> Bool                  -- ^ Whether to reserve literate
     -> TopLevelModuleName    -- ^ Module to be highlighted.
     -> Html
     -> Text
page css
     highlightOccurrences
     htmlHighlight
     modName
     pageContent =
  renderHtml $ if htmlHighlight
               then pageContent
               else Html5.docTypeHtml $ hdr <> rest
  where

    hdr = Html5.head $ mconcat
      [ Html5.meta !! [ Attr.charset "utf-8" ]
      , Html5.title (toHtml . render $ pretty modName)
      , Html5.link !! [ Attr.rel "stylesheet"
                      , Attr.href $ stringValue css
                      ]
      , if highlightOccurrences
        then Html5.script mempty !!
          [ Attr.type_ "text/javascript"
          , Attr.src $ stringValue occurrenceHighlightJsFile
          ]
        else mempty
      ]

    rest = Html5.body $ (Html5.pre ! Attr.class_ "Agda") pageContent

-- | Position, Contents, Infomation

type TokenInfo =
  ( Int
  , String
  , Aspects
  )

-- | Constructs token stream ready to print.

tokenStream
     :: Text             -- ^ The contents of the module.
     -> HighlightingInfo -- ^ Highlighting information.
     -> [TokenInfo]
tokenStream contents info =
  map (\cs -> case cs of
          (mi, (pos, _)) : _ ->
            (pos, map (snd . snd) cs, fromMaybe mempty mi)
          [] -> __IMPOSSIBLE__) $
  List.groupBy ((==) `on` fst) $
  zipWith (\pos c -> (IntMap.lookup pos infoMap, (pos, c))) [1..] (T.unpack contents)
  where
  infoMap = toMap info

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

  -- Proposed in #3373, implemented in #3384
  mkRst :: [TokenInfo] -> Html
  mkRst = mconcat . (toHtml rstDelimiter :) . map go
    where
      go token@(_, s, mi) = if aspect mi == Just Background
        then preEscapedToHtml s
        else mkHtml token

  -- Proposed in #3137, implemented in #3313
  -- Improvement proposed in #3366, implemented in #3367
  mkMd :: [[TokenInfo]] -> Html
  mkMd = mconcat . go
    where
      work token@(_, s, mi) = case aspect mi of
        Just Background -> preEscapedToHtml s
        Just Markup     -> __IMPOSSIBLE__
        _               -> mkHtml token
      go [a, b] = [ mconcat $ work <$> a
                  , Html5.pre ! Attr.class_ "Agda" $ mconcat $ work <$> b
                  ]
      go [a]    = work <$> a
      go _      = __IMPOSSIBLE__

  mkOrg :: [TokenInfo] -> Html
  mkOrg tokens = mconcat $ if containsCode then formatCode else formatNonCode
    where
      containsCode = any ((/= Just Background) . aspect . trd) tokens

      startDelimiter = preEscapedToHtml orgDelimiterStart
      endDelimiter = preEscapedToHtml orgDelimiterEnd

      formatCode = startDelimiter : foldr (\x -> (go x :)) [endDelimiter] tokens
      formatNonCode = map go tokens

      go token@(_, s, mi) = if aspect mi == Just Background
        then preEscapedToHtml s
        else mkHtml token

  -- Put anchors that enable referencing that token.
  -- We put a fail safe numeric anchor (file position) for internal references
  -- (issue #2756), as well as a heuristic name anchor for external references
  -- (issue #2604).
  annotate :: Int -> Aspects -> Html -> Html
  annotate pos mi =
    applyWhen hereAnchor (anchorage nameAttributes mempty <>) . anchorage posAttributes
    where
    -- Warp an anchor (<A> tag) with the given attributes around some HTML.
    anchorage :: [Attribute] -> Html -> Html
    anchorage attrs html = Html5.a html !! attrs

    -- File position anchor (unique, reliable).
    posAttributes :: [Attribute]
    posAttributes = concat
      [ [Attr.id $ stringValue $ show pos ]
      , toList $ link <$> definitionSite mi
      , Attr.class_ (stringValue $ unwords classes) <$ guard (not $ null classes)
      ]

    -- Named anchor (not reliable, but useful in the general case for outside refs).
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

      opClass = ["Operator" | op]
    aspectClasses a = [show a]


    otherAspectClasses = map show

    -- Notes are not included.
    noteClasses _s = []

    -- Should we output a named anchor?
    -- Only if we are at the definition site now (@here@)
    -- and such a pretty named anchor exists (see 'defSiteAnchor').
    hereAnchor      :: Bool
    hereAnchor      = here && isJust mDefSiteAnchor

    mDefinitionSite :: Maybe DefinitionSite
    mDefinitionSite = definitionSite mi

    -- Are we at the definition site now?
    here            :: Bool
    here            = maybe False defSiteHere mDefinitionSite

    mDefSiteAnchor  :: Maybe String
    mDefSiteAnchor  = maybe __IMPOSSIBLE__ defSiteAnchor mDefinitionSite

    link (DefinitionSite m defPos _here _aName) = Attr.href $ stringValue $
      -- If the definition site points to the top of a file,
      -- we drop the anchor part and just link to the file.
      applyUnless (defPos <= 1)
        (++ "#" ++
         Network.URI.Encode.encode (show defPos))
         -- Network.URI.Encode.encode (fromMaybe (show defPos) aName)) -- Named links disabled
        (Network.URI.Encode.encode $ modToFile m "html")
