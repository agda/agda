{-# OPTIONS_GHC -Wunused-imports #-}

-- | Functions which give precise syntax highlighting info to Emacs.

module Agda.Interaction.Highlighting.Emacs
  ( lispifyHighlightingInfo
  , lispifyTokenBased
  ) where

import Prelude hiding (null)

import Agda.Interaction.Highlighting.Common
import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.Highlighting.Range (Range(..))
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
  :: ModuleToSource
     -- ^ Must contain a mapping for the definition site's module, if any.
  -> (Range, Aspects) -> Lisp String
showAspects modFile (r, m) = L $
    (map (A . show) [from r, to r])
      ++
    [L $ map A $ toAtoms m]
      ++
    dropNils (
      [lispifyTokenBased (tokenBased m)]
        ++
      [A $ ifNull (note m) "nil" quote]
        ++
      maybeToList (defSite <$> definitionSite m))
  where
  defSite (DefinitionSite m p _ _) =
    Cons (A $ quote $ filePath f) (A $ show p)
    where f = Map.findWithDefault __IMPOSSIBLE__ m modFile

  dropNils = List.dropWhileEnd (== A "nil")

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
  :: HighlightingInfo
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
             map (showAspects modFile) (toList h)

  direct :: IO (Lisp String)
  direct = return $ L (A "agda2-highlight-add-annotations" :
                         map Q info)

  indirect :: IO (Lisp String)
  indirect = do
    filepath <- writeToTempFile (prettyShow $ L info)
    return $ L [ A "agda2-highlight-load-and-delete-action"
               , A (quote filepath)
               ]
