module Agda.Syntax.Fixity where

import Agda.Syntax.Position ( KillRange )

data Fixity'

instance KillRange Fixity'

noFixity' :: Fixity'
