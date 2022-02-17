
module Agda.Utils.ProfileOptions
  ( ProfileOption(..)
  , ProfileOptions
  , noProfileOptions
  , addProfileOption
  , containsProfileOption
  , profileOptionsToList
  , profileOptionsFromList
  , validProfileOptionStrings
  ) where

import Control.DeepSeq
import Control.Monad
import Data.List (intercalate)
import Data.Char (toLower)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import GHC.Generics (Generic)
import Text.EditDistance (restrictedDamerauLevenshteinDistance, defaultEditCosts)

-- | Various things that can be measured when checking an Agda development. Turned on with
--   the `--profile` flag, for instance `--profile=sharing` to turn on the 'Sharing' option.
--   'Internal', 'Modules', and 'Definitions' are mutually exclusive.
--
--   NOTE: Changing this data type requires bumping the interface version number in
--   'Agda.TypeChecking.Serialise.currentInterfaceVersion'.
data ProfileOption = Internal     -- ^ Measure time taken by various parts of the system (type checking, serialization, etc)
                   | Modules      -- ^ Measure time spent on individual (Agda) modules
                   | Definitions  -- ^ Measure time spent on individual (Agda) definitions
                   | Sharing      -- ^ Measure things related to sharing
                   | Serialize    -- ^ Collect detailed statistics about serialization
                   | Constraints  -- ^ Collect statistics about constraint solving
                   | Metas        -- ^ Count number of created metavariables
                   | Interactive  -- ^ Measure time of interactive commands
  deriving (Show, Eq, Ord, Enum, Bounded, Generic)

instance NFData ProfileOption

-- | A set of 'ProfileOption's
newtype ProfileOptions = ProfileOpts { unProfileOpts :: Set ProfileOption }
  deriving (Show, Eq, NFData)

-- | The empty set of profiling options.
noProfileOptions :: ProfileOptions
noProfileOptions = ProfileOpts Set.empty

addAllProfileOptions :: ProfileOptions -> ProfileOptions
addAllProfileOptions (ProfileOpts opts) = ProfileOpts $ foldl ins opts [minBound..maxBound]
  where
    ins os o | any (incompatible o) os = os
             | otherwise               = Set.insert o os

-- | Strings accepted by 'addProfileOption'
validProfileOptionStrings :: [String]
validProfileOptionStrings = "all" : map optName [minBound .. maxBound :: ProfileOption]

parseOpt :: String -> Either String ProfileOption
parseOpt = \ s -> case Map.lookup s names of
    Nothing -> Left $ err s
    Just o  -> Right o
  where
    names = Map.fromList [ (optName o, o) | o <- [minBound .. maxBound] ]

    close s t = restrictedDamerauLevenshteinDistance defaultEditCosts s t <= 3
    err  s = concat ["Not a valid profiling option: '", s, "'. ", hint s]
    hint s = case filter (close s) (Map.keys names) of
               [] -> concat [ "Valid options are ", intercalate ", " $ Map.keys names, ", or all." ]
               ss -> concat [ "Did you mean ", intercalate " or " ss, "?" ]

optName :: ProfileOption -> String
optName = map toLower . show

incompatible :: ProfileOption -> ProfileOption -> Bool
incompatible o1 o2
  | o1 == o2  = False
  | otherwise = any (\ set -> elem o1 set && elem o2 set) sets
  where
    sets = [[Internal, Modules, Definitions]]

-- | Parse and add a profiling option to a set of profiling options. Returns `Left` with a helpful
--   error message if the option doesn't parse or if it's incompatible with existing options.
--   The special string "all" adds all options compatible with the given set and prefering the first
--   of incompatible options. So `--profile=all` sets 'Internal' over 'Modules' and 'Definitions',
--   but `--profile=modules --profile=all` sets 'Modules' and not 'Internal'.
addProfileOption :: String -> ProfileOptions -> Either String ProfileOptions
addProfileOption "all" opts = pure $ addAllProfileOptions opts
addProfileOption s (ProfileOpts opts) = do
  o <- parseOpt s
  let conflicts = filter (incompatible o) (Set.toList opts)
  unless (null conflicts) $ Left $ concat ["Cannot use profiling option '", s, "' with '", optName $ head $ conflicts, "'"]
  return $ ProfileOpts $ Set.insert o opts

-- | Check if a given profiling option is present in a set of profiling options.
containsProfileOption :: ProfileOption -> ProfileOptions -> Bool
containsProfileOption o (ProfileOpts opts) = Set.member o opts

-- | Use only for serialization.
profileOptionsToList :: ProfileOptions -> [ProfileOption]
profileOptionsToList (ProfileOpts opts) = Set.toList opts

-- | Use only for serialization.
profileOptionsFromList :: [ProfileOption] -> ProfileOptions
profileOptionsFromList opts = ProfileOpts $ Set.fromList opts

