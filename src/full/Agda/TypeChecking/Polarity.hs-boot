
module Agda.TypeChecking.Polarity where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base

computePolarity :: [QName] -> TCM ()
composePol      :: Polarity -> Polarity -> Polarity
