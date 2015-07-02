module Agda.Syntax.Fixity where

import Agda.Syntax.Position ( KillRange )

data Fixity'

instance KillRange Fixity'
instance Show Fixity'

noFixity' :: Fixity'
