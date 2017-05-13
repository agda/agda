module Agda.Syntax.Fixity where

import Control.DeepSeq (NFData)
import Data.Data (Data)

import Agda.Syntax.Position ( KillRange )

data Fixity'

instance KillRange Fixity'
instance Data Fixity'
instance NFData Fixity'
instance Show Fixity'

noFixity' :: Fixity'
