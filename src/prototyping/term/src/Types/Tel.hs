
module Types.Tel where

import IMPL.Term
import Types.Abs

data Telescope = EmptyTel | Type :> Abs Telescope
  deriving Show

telSize :: Telescope -> Int
telSize EmptyTel   = 0
telSize (_ :> tel) = 1 + telSize (absBody tel)
