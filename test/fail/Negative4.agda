module Negative4 where

data Empty : Set where

data NSPos : Set where
   c : ((NSPos -> Empty) -> NSPos) -> NSPos



