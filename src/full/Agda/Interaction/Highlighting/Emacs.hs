{-# LANGUAGE CPP #-}

-- | Functions which give precise syntax highlighting info to Emacs.

module Agda.Interaction.Highlighting.Emacs
  ( showHighlightingInfo
  , lispifyHighlightingInfo
  , Agda.Interaction.Highlighting.Emacs.tests
  ) where

import Agda.Interaction.FindFile
import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.Highlighting.Range
import Agda.Interaction.EmacsCommand
import Agda.Syntax.Abstract (QName)
import Agda.Syntax.Common
import qualified Agda.Syntax.Position as P
import Agda.Syntax.Translation.ConcreteToAbstract (TopLevelInfo)
import Agda.TypeChecking.Errors (prettyError)
import Agda.Utils.FileName
import Agda.Utils.String
import Agda.Utils.TestHelpers

import Agda.Utils.Impossible
#include "../../undefined.h"

import Control.Monad.Trans
import Data.List
import qualified Data.Map as Map
import Data.Char
import Data.Maybe

------------------------------------------------------------------------
-- Read/show functions

-- | Converts the 'aspect' and 'otherAspects' fields to atoms readable
-- by the Emacs interface.

toAtoms :: MetaInfo -> [String]
toAtoms m = map toAtom (otherAspects m) ++ toAtoms' (aspect m)
  where
  toAtom x = map toLower (show x)

  kindToAtom (Constructor Inductive)   = "inductiveconstructor"
  kindToAtom (Constructor CoInductive) = "coinductiveconstructor"
  kindToAtom k                         = toAtom k

  toAtoms' Nothing               = []
  toAtoms' (Just (Name mKind op)) =
    map kindToAtom (maybeToList mKind) ++ opAtom
    where opAtom | op        = ["operator"]
                 | otherwise = []
  toAtoms' (Just a) = [toAtom a]

-- | Shows meta information in such a way that it can easily be read
-- by Emacs.

showMetaInfo :: ModuleToSource
                -- ^ Must contain a mapping for the definition site's
                -- module, if any.
             -> (Range, MetaInfo) -> Lisp String
showMetaInfo modFile (r, m) =
    L $ ((map (A . show) [from r, to r])
           ++
         [L $ map A $ toAtoms m]
           ++
         (A $ maybe "nil" quote $ note m)
         :
          defSite)
  where
  defSite = case definitionSite m of
    Nothing     -> []
    Just (m, p) -> case Map.lookup m modFile of
      Nothing -> __IMPOSSIBLE__
      Just f  -> [Cons (A $ quote $ filePath f) (A $ show p)]

-- | Shows syntax highlighting information in an Emacsy fashion.

showHighlightingInfo
  :: (HighlightingInfo, ModuleToSource)
     -- ^ The 'ModuleToSource' must contain a mapping for every
     -- definition site's module.
  -> String
showHighlightingInfo (h, modFile) = show $
  L $ map (showMetaInfo modFile) (ranges h)

-- | Turns syntax highlighting information into a list of
-- S-expressions.
--
-- Precondition: The 'definitionSite's in the highlighting information
-- must be @Nothing@.

lispifyHighlightingInfo :: HighlightingInfo -> Lisp String
lispifyHighlightingInfo file =
  L (A "agda2-typechecking-emacs" :
     map (showMetaInfo __IMPOSSIBLE__) (ranges file))

------------------------------------------------------------------------
-- All tests

-- TODO: One could check that the show functions are invertible.

-- | All the properties.

tests :: IO Bool
tests = runTests "Agda.Interaction.Highlighting.Emacs" []
