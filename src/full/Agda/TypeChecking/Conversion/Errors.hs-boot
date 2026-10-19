module Agda.TypeChecking.Conversion.Errors where

import Control.DeepSeq

data ConversionError
instance Show ConversionError
instance NFData ConversionError
