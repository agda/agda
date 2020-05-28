-- | Pretty printing of interface files

module Agda.Interaction.PrettyPrintInterface where

import Control.Monad.State

import Data.Maybe

import Agda.Interaction.Options
import Agda.TypeChecking.Monad

import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Impossible

-- | Pretty print the given 'Interface' to the file specified by the
--   command line option.
prettyPrint :: Interface -> TCM ()
prettyPrint interface = do
    fp <- fromMaybe __IMPOSSIBLE__ . optPrettyPrintInterface <$> commandLineOptions
    liftIO $ writeFile fp $ prettyPrintedInterface
  where
    prettyPrintedInterface :: String
--    prettyPrintedInterface = "Hej"
    prettyPrintedInterface = prettyShow interface
