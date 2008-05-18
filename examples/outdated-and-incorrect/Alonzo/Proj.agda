module Proj where
open import AlonzoPrelude

showTrue : True -> String
showTrue _ = "tt"

-- data True : Set where
--   tt : True

data T4 : Set where
  C : True -> True -> True -> True -> T4

g : True -> True -> True
g x y = tt

f14 : T4 -> True -> True
f14 (C x y z t) = \w -> g x t

mainS : String
mainS = showTrue $ (id ○ f14) (C tt tt tt tt) tt