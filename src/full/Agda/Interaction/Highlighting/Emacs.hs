
-- | Functions which give precise syntax highlighting info to Emacs.

module Agda.Interaction.Highlighting.Emacs
  ( lispifyHighlightingInfo
  , lispifyTokenBased
  ) where

import Prelude hiding (null)

import Agda.Interaction.Highlighting.Common
import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.Highlighting.Range (Range(..), Ranges)
import Agda.Interaction.EmacsCommand
import Agda.Interaction.Response
import Agda.TypeChecking.Monad (HighlightingMethod(..), ModuleToSource)
import Agda.Utils.FileName (filePath)
import Agda.Utils.IO.TempFile (writeToTempFile)
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.String (quote)

import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe

import Agda.Utils.Null
import Agda.Utils.Impossible

------------------------------------------------------------------------
-- Read/show functions

-- | Shows meta information in such a way that it can easily be read
-- by Emacs.

showAspects
  :: Bool
     -- ^ Only generate a result when there is some relevant data.
     -- (Note that the Emacs commands
     -- @agda2-highlight-add-annotations@ and
     -- @agda2-highlight-load-and-delete-action@ may remove
     -- highlighting information for ranges without \"annotations\".)
  -> ModuleToSource
     -- ^ Must contain a mapping for the definition site's module, if any.
  -> (Range, Aspects) -> Maybe (Lisp String)
showAspects skipEmpty modFile (r, m)
  | skipEmpty && noInfo = Nothing
  | otherwise           = Just $ L $
    (map (A . show) [from r, to r])
      ++
    [L $ map A $ toAtoms m]
      ++
    dropNils (
      [lispifyTokenBased (tokenBased m)]
        ++
      [A $ ifNull (note m) "nil" quote]
        ++
      maybeToList defSite)
  where
  defSite = case definitionSite m of
    Nothing                            -> Nothing
    Just (DefinitionSite m p _ _ link) ->
      if not link
      then Nothing
      else Just (Cons (A $ quote $ filePath f) (A $ show p))
      where f = Map.findWithDefault __IMPOSSIBLE__ m modFile

  dropNils = List.dropWhileEnd (== A "nil")

  noInfo =
    isNothing (aspect m) &&
    null (otherAspects m) &&
    isNothing defSite

-- | Formats the 'TokenBased' tag for the Emacs backend. No quotes are
-- added.

lispifyTokenBased :: TokenBased -> Lisp String
lispifyTokenBased TokenBased        = A "t"
lispifyTokenBased NotOnlyTokenBased = A "nil"

-- | Turns syntax highlighting information into a list of
-- S-expressions.

-- TODO: The "go-to-definition" targets can contain long strings
-- (absolute paths to files). At least one of these strings (the path
-- to the current module) can occur many times. Perhaps it would be a
-- good idea to use a more compact format.

lispifyHighlightingInfo
  :: Either Ranges HighlightingInfo
     -- ^ @'Left' rs@: Remove highlighting from the ranges @rs@.
  -> RemoveTokenBasedHighlighting
  -> HighlightingMethod
  -> ModuleToSource
     -- ^ Must contain a mapping for every definition site's module.
  -> IO (Lisp String)
lispifyHighlightingInfo h remove method modFile =
  case chooseHighlightingMethod h method of
    Direct   -> direct
    Indirect -> indirect
  where
  info :: [Lisp String]
  info = (case remove of
                RemoveHighlighting -> A "remove"
                KeepHighlighting   -> A "nil") :
         catMaybes (map (showAspects skipEmpty modFile) (toList h'))
    where
    (skipEmpty, h') = case h of
      Right h -> (True,  h)
      Left rs -> (False, singleton rs mempty)

  direct :: IO (Lisp String)
  direct = return $ L (A "agda2-highlight-add-annotations" :
                         map Q info)

  indirect :: IO (Lisp String)
  indirect = do
    filepath <- writeToTempFile (prettyShow $ L info)
    return $ L [ A "agda2-highlight-load-and-delete-action"
               , A (quote filepath)
               ]
