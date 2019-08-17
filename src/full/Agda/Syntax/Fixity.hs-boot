module Agda.Syntax.Fixity where

import Control.DeepSeq (NFData)
import Data.Data (Data)

import Agda.Syntax.Common   ( LensFixity )
import Agda.Syntax.Position ( KillRange )
import Agda.Utils.Lens      ( Lens' )

data Fixity'

class LensFixity' a where
  lensFixity' :: Lens' Fixity' a

instance LensFixity Fixity'
instance KillRange Fixity'
instance Data Fixity'
instance NFData Fixity'
instance Show Fixity'

noFixity' :: Fixity'
