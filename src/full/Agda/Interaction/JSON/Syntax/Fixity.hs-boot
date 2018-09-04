module Agda.Interaction.JSON.Syntax.Fixity where

import Data.Aeson (ToJSON)
import Agda.Syntax.Fixity (Fixity')

instance ToJSON Fixity'
