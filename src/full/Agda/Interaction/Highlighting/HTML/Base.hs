
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
import Control.Monad.State
import Control.Monad.Trans ( MonadIO(..), lift )
import Control.Monad.Trans.Reader ( ReaderT(runReaderT), ask )

import Data.Function ( on )
import Data.Foldable (toList, concatMap)
import Data.Maybe
import qualified Data.IntMap as IntMap
import qualified Data.List   as List
import Data.List.Split (splitWhen, chunksOf)
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import qualified Data.Text.Lazy as TL
import qualified Data.Text as T

import GHC.Generics (Generic)

import qualified Network.URI.Encode

import System.FilePath
import System.Directory

import Text.Blaze.Html5
    ( preEscapedToHtml
    , toHtml
    , stringValue
    , textValue
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

import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Common

import qualified Agda.TypeChecking.Monad as TCM
  ( Interface(..)
  )
import Agda.TypeChecking.Monad.Debug

import Agda.Utils.Function
import qualified Agda.Utils.Functor as F
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
  { _srcFileModuleName :: C.TopLevelModuleName
  , _srcFileType :: FileType
  -- ^ Source file type
  , _srcFileText :: TL.Text
  -- ^ Source text
  , _srcFileHighlightInfo :: HighlightingInfo
  -- ^ Highlighting info
  }

-- | Bundle up the highlighting info for a source file

srcFileOfInterface :: C.TopLevelModuleName -> TCM.Interface -> HtmlInputSourceFile
srcFileOfInterface m i = HtmlInputSourceFile m (TCM.iFileType i) (TCM.iSource i) (TCM.iHighlighting i)

-- | An HTML generation monad transformer.
--
-- The state component is used to keep track of all \"symbolic
-- anchors\" that have been used. If an attempt is made to reuse a
-- given symbolic anchor, then an internal error is raised.

type HtmlM m a = StateT (HashSet T.Text) m a

-- | Logging during HTML generation

type HtmlLogMessage = String
type HtmlLogAction m = HtmlLogMessage -> m ()

class Monad m => MonadLogHtml m where
  logHtml :: HtmlLogAction m

type LogHtmlT m = ReaderT (HtmlLogAction m) m

instance Monad m => MonadLogHtml (LogHtmlT m) where
  logHtml message = do
    doLog <- ask
    lift $ doLog message

runLogHtmlWith :: Monad m => HtmlLogAction m -> LogHtmlT m a -> m a
runLogHtmlWith = flip runReaderT

renderSourceFile ::
  MonadDebug m => HtmlOptions -> HtmlInputSourceFile -> HtmlM m TL.Text
renderSourceFile opts = renderSourcePage
  where
  cssFile = fromMaybe defaultCSSFile (htmlOptCssFile opts)
  highlightOccur = htmlOptHighlightOccurrences opts
  htmlHighlight = htmlOptHighlight opts
  renderSourcePage (HtmlInputSourceFile moduleName fileType sourceCode hinfo) =
    page cssFile highlightOccur onlyCode moduleName <$> pageContents
    where
      tokens = tokenStream sourceCode hinfo
      onlyCode = highlightOnlyCode htmlHighlight fileType
      pageContents = code onlyCode fileType tokens

defaultPageGen ::
  (MonadDebug m, MonadIO m, MonadLogHtml m) =>
  HtmlOptions -> HtmlInputSourceFile -> m ()
defaultPageGen opts srcFile@(HtmlInputSourceFile moduleName ft _ _) = do
  logHtml $ render $ "Generating HTML for"  <+> pretty moduleName <+> ((parens (pretty target)) <> ".")
  html <- evalStateT html Set.empty
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

modToFile :: C.TopLevelModuleName -> String -> FilePath
modToFile m ext = Network.URI.Encode.encode $ render (pretty m) <.> ext

-- | Generates a highlighted, hyperlinked version of the given module.

writeRenderedHtml
  :: MonadIO m
  => TL.Text    -- ^ Rendered page
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
     -> C.TopLevelModuleName  -- ^ Module to be highlighted.
     -> Html
     -> TL.Text
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
     :: TL.Text          -- ^ The contents of the module.
     -> HighlightingInfo -- ^ Highlighting information.
     -> [TokenInfo]
tokenStream contents info =
  map (\cs -> case cs of
          (mi, (pos, _)) : _ ->
            (pos, map (snd . snd) cs, fromMaybe mempty mi)
          [] -> __IMPOSSIBLE__) $
  List.groupBy ((==) `on` fst) $
  zipWith (\pos c -> (IntMap.lookup pos infoMap, (pos, c))) [1..]
    (TL.unpack contents)
  where
  infoMap = toMap info

-- | Constructs the HTML displaying the code.

code
  :: forall m. MonadDebug m
  => Bool     -- ^ Whether to generate non-code contents as-is
  -> FileType -- ^ Source file type
  -> [TokenInfo]
  -> HtmlM m Html
code onlyCode fileType = mconcat F.<.> if onlyCode
  then case fileType of
         -- Explicitly written all cases, so people
         -- get compile error when adding new file types
         -- when they forget to modify the code here
         RstFileType  -> mapM mkRst . splitByMarkup
         MdFileType   -> mapM mkMd . chunksOf 2 . splitByMarkup
         AgdaFileType -> mapM mkHtml
         -- Any points for using this option?
         TexFileType  -> mapM mkMd . chunksOf 2 . splitByMarkup
         OrgFileType  -> mapM mkOrg . splitByMarkup
  else mapM mkHtml
  where
  trd (_, _, a) = a

  splitByMarkup :: [TokenInfo] -> [[TokenInfo]]
  splitByMarkup = splitWhen $ (== Just Markup) . aspect . trd

  mkHtml :: TokenInfo -> HtmlM m Html
  mkHtml (pos, s, mi) =
    -- Andreas, 2017-06-16, issue #2605:
    -- Do not create anchors for whitespace.
    applyUnless (mi == mempty) (annotate pos mi =<<) (return (toHtml s))

  -- Proposed in #3373, implemented in #3384
  mkRst :: [TokenInfo] -> HtmlM m Html
  mkRst = (mconcat . (toHtml rstDelimiter :)) F.<.> mapM go
    where
      go token@(_, s, mi) = if aspect mi == Just Background
        then return (preEscapedToHtml s)
        else mkHtml token

  -- Proposed in #3137, implemented in #3313
  -- Improvement proposed in #3366, implemented in #3367
  mkMd :: [[TokenInfo]] -> HtmlM m Html
  mkMd = mconcat F.<.> go
    where
      work token@(_, s, mi) = case aspect mi of
        Just Background -> return (preEscapedToHtml s)
        Just Markup     -> __IMPOSSIBLE__
        _               -> mkHtml token
      go [a, b] = sequence
                    [ mconcat <$> mapM work a
                    , (Html5.pre ! Attr.class_ "Agda") . mconcat <$>
                      mapM work b
                    ]
      go [a]    = mapM work a
      go _      = __IMPOSSIBLE__

  mkOrg :: [TokenInfo] -> HtmlM m Html
  mkOrg tokens =
    mconcat <$> if containsCode then formatCode else formatNonCode
    where
      containsCode = any ((/= Just Background) . aspect . trd) tokens

      startDelimiter = preEscapedToHtml orgDelimiterStart
      endDelimiter = preEscapedToHtml orgDelimiterEnd

      formatCode =
        ([startDelimiter] ++) . (++ [endDelimiter]) <$> formatNonCode
      formatNonCode = mapM go tokens

      go token@(_, s, mi) = if aspect mi == Just Background
        then return (preEscapedToHtml s)
        else mkHtml token

  -- Inserts anchors (HTML identifiers) that make it possible to refer
  -- to the given token. Numeric anchors are always inserted, and
  -- sometimes also symbolic ones, based on the names of Agda
  -- identifiers.
  annotate :: Int -> Aspects -> Html -> HtmlM m Html
  annotate pos mi h = do
    h <- return $ anchorage posAttributes h
    if not anchor then return h else
      case mDefSiteAnchor of
        Nothing -> __IMPOSSIBLE__
        Just a  -> do
          duplicate <- gets (Set.member a)
          when duplicate $ __IMPOSSIBLE_VERBOSE__ $
            "Duplicate symbolic anchor: " ++ T.unpack a
          modify' (Set.insert a)
          return (anchorage nameAttributes mempty <> h)
    where
    -- Warp an anchor (<A> tag) with the given attributes around some HTML.
    anchorage :: [Attribute] -> Html -> Html
    anchorage attrs html = Html5.a html !! attrs

    -- File position anchor (unique, reliable).
    posAttributes :: [Attribute]
    posAttributes = concat
      [ [Attr.id $ stringValue $ show pos ]
      , toList $ link =<< definitionSite mi
      , Attr.class_ (stringValue $ unwords classes) <$ guard (not $ null classes)
      ]

    -- Named anchor (not reliable, but useful in the general case for outside refs).
    nameAttributes :: [Attribute]
    nameAttributes = [ Attr.id $ textValue $ fromMaybe __IMPOSSIBLE__ $ mDefSiteAnchor ]

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
      showKind (Module _)                = "Module"
      showKind k                         = show k

      opClass = ["Operator" | op]
    aspectClasses a = [show a]


    otherAspectClasses = map show

    -- Notes are not included.
    noteClasses _s = []

    -- Should we output a named anchor?
    anchor :: Bool
    anchor = maybe False defSiteId (definitionSite mi) &&
               isJust mDefSiteAnchor

    mDefSiteAnchor :: Maybe T.Text
    mDefSiteAnchor =
      maybe __IMPOSSIBLE__ (T.pack F.<.> defSiteAnchor)
        (definitionSite mi)

    link d
      | not (defSiteLink d) = Nothing
      | otherwise           = Just $ Attr.href $ stringValue $
        -- If the definition site points to the top of a file, then we
        -- drop the anchor part and just link to the file.
        applyUnless (defSitePos d <= 1)
          (++ "#" ++
           Network.URI.Encode.encode
           -- Links currently do not point to symbolic identifiers.
           -- (fromMaybe (show (defSitePos d)) (defSiteAnchor d))
             (show (defSitePos d)))
          (Network.URI.Encode.encode
             (modToFile (defSiteModule d) "html"))
