{-# LANGUAGE CPP #-}

-- | Functions which give precise syntax highlighting info to Emacs.

module Agda.Interaction.Highlighting.Emacs
  ( lispifyHighlightingInfo
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
import Agda.TypeChecking.Monad
  (TCM, envHighlightingMethod, HighlightingMethod(..))
import Agda.Utils.FileName
import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.String
import Agda.Utils.TestHelpers

import Agda.Utils.Impossible
#include "../../undefined.h"

import Control.Applicative
import qualified Control.Exception as E
import Control.Monad.Reader
import Control.Monad.Trans
import Data.Char
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import qualified System.Directory as D
import qualified System.IO as IO

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
  info     = map (showMetaInfo modFile) (ranges h)

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
