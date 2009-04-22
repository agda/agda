
module Issue113 where

module X where

  postulate D : Set

open X public

postulate x : D

-- Should give the proper error message, not __IMPOSSIBLE__ from Highlight.Generate
typeIncorrect : Set
typeIncorrect = Set1
