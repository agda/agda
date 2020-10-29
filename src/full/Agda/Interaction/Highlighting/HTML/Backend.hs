
-- | Backend for generating highlighted, hyperlinked HTML from Agda sources.

module Agda.Interaction.Highlighting.HTML.Backend
  ( generateHTML
  ) where

import Agda.Interaction.Highlighting.HTML.Base

import Prelude hiding ((!!), concatMap)

import qualified Data.Map as Map

import Agda.Interaction.Options (CommandLineOptions(..))

import Agda.TypeChecking.Monad
  ( MonadDebug
  , reportS
  , miInterface
  , getVisitedModules
  , commandLineOptions
  , TCM
  )

runLogHtmlWithMonadDebug :: MonadDebug m => LogHtmlT m a -> m a
runLogHtmlWithMonadDebug = runLogHtmlWith $ reportS "html" 1

htmlOptsFromCliOpts :: CommandLineOptions -> HtmlOptions
htmlOptsFromCliOpts opts = HtmlOptions
  { htmlOptDir = optHTMLDir opts
  , htmlOptHighlight = optHTMLHighlight opts
  , htmlOptHighlightOccurrences = optHighlightOccurrences opts
  , htmlOptCssFile = optCSSFile opts
  }

-- | Generates HTML files from all the sources which have been
--   visited during the type checking phase.
--
--   This function should only be called after type checking has
--   completed successfully.
generateHTML :: TCM ()
generateHTML = do
  opts <- htmlOptsFromCliOpts <$> commandLineOptions
  pages <- fmap (\(n, mi) -> srcFileOfInterface n (miInterface mi))
        <$> (Map.toList <$> getVisitedModules)
  runLogHtmlWithMonadDebug $ generateHTMLPages opts pages
