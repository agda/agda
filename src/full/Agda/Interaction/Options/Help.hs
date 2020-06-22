
module Agda.Interaction.Options.Help
       (
         Help (..)
       , helpTopicUsage
       , string2HelpTopic
       , allHelpTopics
       ) where

import Agda.Interaction.Options.Warnings

-- | Interface to the @help@ function
data Help
  = GeneralHelp
  -- ^ General usage information
  | HelpFor HelpTopic
  -- ^ Specialised usage information about TOPIC
  deriving (Eq, Show)

-- | List of Help Topics
-- NOTA BENE:
-- You need to add each new topic together with its name to @allHelpTopics@

data HelpTopic
  = Warning
  deriving (Eq, Show)

allHelpTopics :: [(String, HelpTopic)]
allHelpTopics = [("warning", Warning)]

-- | Usage information generation

helpTopicUsage :: HelpTopic -> String
helpTopicUsage tp = case tp of
  Warning -> usageWarning

-- | Conversion functions to strings

string2HelpTopic :: String -> Maybe HelpTopic
string2HelpTopic str = lookup str allHelpTopics

-- UNUSED Liang-Ting Chen 2019-07-15
--helpTopic2String :: HelpTopic -> String
--helpTopic2String w = fromMaybe __IMPOSSIBLE__ $ lookup w (map swap allHelpTopics)
--
