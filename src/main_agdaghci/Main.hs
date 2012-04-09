-- | Wrapper for "Agda.Interaction.GhcTop.main".
--
-- Agda is installed as a library. This module is used to build the
-- executable which is needed for the Emacs frontend.

module Main (main) where

import qualified Agda.Interaction.GhcTop ( main )
import Prelude ( IO )

main :: IO ()
main = Agda.Interaction.GhcTop.main
