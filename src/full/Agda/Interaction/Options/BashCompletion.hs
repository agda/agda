-- | Tools for shell completion scripts.

module Agda.Interaction.Options.BashCompletion where

import Data.Map qualified as Map
import Data.Maybe

import Agda.Interaction.Options.Arguments (optionValues)
import Agda.Interaction.Options.Base (standardOptions_)
import Agda.Interaction.Options.ProfileOptions (validProfileOptionStrings)

import Agda.Utils.GetOpt (OptDescr(..), ArgDescr(..))

printedOptions :: [String]
printedOptions = printOptions standardOptions_

-- | Print just the names of the given options (e.g. for bash completion scripts).
--   For long options with finitely enumerable arguments, print all variants.
printOptions :: [OptDescr ()] -> [String]
printOptions = concat . map \case
  Option short long arg _help -> concat $
    ss :
    ls :
    [ [ s        ++ a | s <- ss ] ++
      [ l ++ "=" ++ a | l <- ls ]
    | a <- as
    ]
    where
      ss :: [String]
      ss = [ '-' : s : "" | s <- short ]
      ls :: [String]
      ls = [ "--" ++ l | l <- long ]
      as :: [String]
      as = fromMaybe [] do
        t <- argType
        Map.lookup t optionValues
      argType :: Maybe String
      argType = case arg of
        NoArg{}     -> Nothing
        ReqArg _ t -> Just t
        OptArg _ t -> Just t
