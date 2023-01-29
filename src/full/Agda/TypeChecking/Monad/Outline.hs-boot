module Agda.TypeChecking.Monad.Outline where

import Agda.Utils.FileName
import Control.DeepSeq

data OutlineOutputCallback
data OutlineEntry

instance NFData OutlineOutputCallback
instance NFData OutlineEntry
