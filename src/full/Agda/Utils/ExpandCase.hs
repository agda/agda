
module Agda.Utils.ExpandCase where

class ExpandCase a where
  type Result a
  expand :: ((a -> Result a) -> Result a) -> a
