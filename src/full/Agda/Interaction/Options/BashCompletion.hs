{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wunused-matches #-}
{-# OPTIONS_GHC -Wunused-binds   #-}

-- | Tools for shell completion scripts.
--
-- Bash completion takes a list of completion words (the current commandline)
-- and a completion index (the current word to be completed) and returns
-- a list of possible completions of this word.
--
-- To do bash completion /inside/ Agda, we need to pass this data to Agda.
-- So we equip Agda with a special option @--bash-completion@ which takes
-- first the completion index (number) and then the completion words.
-- E.g.
--
-- @
--    agda --bash-completion 1 --warn
-- @
--
-- This should complete @--warn@ to @--warning=@.
--
-- @
--    agda --bash-completion 1 --warning=
-- @
--
-- This would list the possible values for WARNING.
-- However, these are too many and one may get the annoying question
-- whether one really wants to see all.
-- So we should only produce a small enough list.
-- We show the common prefixes of all values up to a maximal number (threshold).
-- To this end, we may store the possible completion as a compressed trie
-- where instead of letters we use maximal non-overlapping prefixes.
-- Then we compute a fair truncation of the tree so that the
-- total number of leaves stay below the threshold.

module Agda.Interaction.Options.BashCompletion where

import Prelude hiding (null)

import Data.Bifunctor ( first )
import Data.Map       qualified as Map
import Data.Maybe
import Text.Read      ( readMaybe )

import Agda.Interaction.Options.Arguments      ( optionValues )
import Agda.Interaction.Options.Base           ( standardOptions )

import Agda.Utils.Function       ( applyWhenJust )
import Agda.Utils.GetOpt         ( OptDescr(..), ArgDescr(..) )
import Agda.Utils.List           ( (!!!) )
import Agda.Utils.List1          qualified as List1
import Agda.Utils.Null
import Agda.Utils.Trie           (Trie)
import Agda.Utils.Trie           qualified as Trie
import Agda.Utils.CompressedTrie qualified as CompressedTrie

type Help = String

printedOptions :: [String]
printedOptions = map fst printedOptionsWithHelp

printedOptionsWithHelp :: [(String, Help)]
printedOptionsWithHelp = printOptions standardOptions

-- | Print just the names of the given options (e.g. for bash completion scripts).
--   For long options with finitely enumerable arguments, print all variants.
printOptions :: [OptDescr a] -> [(String, Help)]
printOptions = concat . map \case
  Option short long arg help -> concat $
    map (,help) ss :
    map (,help) ls :
    map (map (,noHelp))
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
      noHelp :: Help
      noHelp = ""

-- | Should the 'completions' be truncated to a given maximum number of prefixes?
type Truncate = Maybe Int

-- | Handle the option @--bash-complete@.
--   It expects the index @COMP_CWORD@ as first argument
--   that tells which of the following arguments @COMP_WORDS@
--   is supposed to be completed.
--
--   It either returns an error message or the result for @COMPREPLY@.
--
bashComplete ::
     Truncate
       -- ^ Truncate completions suggestions?  To how many?
  -> [String]
       -- ^ Arguments following @--bash-complete@.
  -> Either String String
       -- ^ Error or @COMPREPLY@.
bashComplete tr = \case
  cword : words
    | Just i <- readMaybe cword
    , length words > i
    , Just w <- words !!! i
    -> case complete tr w of
        Completion (Just s) _ -> return s
        Completion ms cs ->
          return $ unlines $ concat
            [ maybeToList ms
            , map fst cs
            ]
  _args -> Left "Error: Wrong invokation of --bash-complete"

-- | The result of an invokation of (bash) completion.
data Completion = Completion
  { extended :: Maybe String
      -- ^ If 'Nothing', then the completion word cannot become a valid option ever.
  , completions :: [(String, Help)]
      -- ^ If 'null', the 'extended' word cannot be further completed.
  }

-- | Cached trie of options.
optionsTrie :: Trie Char Help
optionsTrie = Trie.fromList printedOptionsWithHelp

-- | Complete the given word as an option.
complete :: Truncate -> String -> Completion
complete trunc s
  -- No completion possible?
  | null t =
      Completion Nothing []
  -- Unambiguously (partially) complete by at least one letter.
  | Just (k, _t') <- CompressedTrie.isSingleBranch t =
      Completion (Just $ s ++ List1.toList k) compls
  -- No unambiguous completion possible: just return suggestions.
  | otherwise =
      Completion Nothing compls
  where
    -- The possible suffixes.
    t = CompressedTrie.compress $ Trie.delete [] $ Trie.lookupTrie s optionsTrie
    -- The possibly truncated list of completions.
    compls = map (first (s ++)) $ CompressedTrie.toList $ CompressedTrie.substLeaves f tt
      where
        -- t truncated.
        tt = applyWhenJust trunc CompressedTrie.truncateSizeWithLeaves t
        -- Replace empty leaves by "..." branches.
        f = maybe (CompressedTrie.singleton "..." empty) CompressedTrie.root
