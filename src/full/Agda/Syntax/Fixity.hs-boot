module Agda.Syntax.Fixity where

import Control.DeepSeq (NFData)

import Agda.Syntax.Position ( KillRange )

data Fixity'

instance KillRange Fixity'
instance NFData Fixity'
instance Show Fixity'

noFixity' :: Fixity'
