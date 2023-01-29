module Agda.TypeChecking.Monad.Outline where

import Agda.Utils.FileName
import Control.DeepSeq

data OutlineOutputCallback
data OutlinePending

defaultOutlineOutputCallback :: OutlineOutputCallback
jsonOutlineOutputCallback :: AbsolutePath -> OutlineOutputCallback

instance NFData OutlineOutputCallback
instance NFData OutlinePending
