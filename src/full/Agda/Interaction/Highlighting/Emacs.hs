{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ >= 800
{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
#endif

-- | Functions which give precise syntax highlighting info to Emacs.

module Agda.Interaction.Highlighting.Emacs
  ( lispifyHighlightingInfo
  , Agda.Interaction.Highlighting.Emacs.tests
  ) where

import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.Highlighting.Range
import Agda.Interaction.EmacsCommand
import Agda.Syntax.Common
import Agda.TypeChecking.Monad
  (TCM, envHighlightingMethod, HighlightingMethod(..), ModuleToSource)
import Agda.Utils.FileName
import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.String
import Agda.Utils.TestHelpers

import Control.Applicative
import qualified Control.Exception as E
import Control.Monad.Reader
import Data.Char
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import qualified System.Directory as D
import qualified System.IO as IO

#include "undefined.h"
import Agda.Utils.Impossible

------------------------------------------------------------------------
-- Read/show functions

-- | Converts the 'aspect' and 'otherAspects' fields to atoms readable
-- by the Emacs interface.

toAtoms :: Aspects -> [String]
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

showAspects
  :: ModuleToSource
     -- ^ Must contain a mapping for the definition site's module, if any.
  -> (Range, Aspects) -> Lisp String
showAspects modFile (r, m) =
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

-- | Turns syntax highlighting information into a list of
-- S-expressions.

lispifyHighlightingInfo
  :: HighlightingInfo
  -> ModuleToSource
     -- ^ Must contain a mapping for every definition site's module.
  -> TCM (Lisp String)
lispifyHighlightingInfo h modFile = do
  method <- envHighlightingMethod <$> ask
  liftIO $ case ranges h of
    _             | method == Direct                   -> direct
    ((_, mi) : _) | otherAspects mi == [TypeChecks] ||
                    mi == mempty                       -> direct
    _                                                  -> indirect
  where
  info     = map (showAspects modFile) (ranges h)

  direct   = return $ L (A "agda2-highlight-add-annotations" :
                         map Q info)

  indirect = do
    dir <- D.getTemporaryDirectory
    f   <- E.bracket (IO.openTempFile dir "agda2-mode")
                     (IO.hClose . snd) $ \ (f, h) -> do
             UTF8.hPutStr h (show $ L info)
             return f
    return $ L [ A "agda2-highlight-load-and-delete-action"
               , A (quote f)
               ]

------------------------------------------------------------------------
-- All tests

-- TODO: One could check that the show functions are invertible.

-- | All the properties.

tests :: IO Bool
tests = runTests "Agda.Interaction.Highlighting.Emacs" []
