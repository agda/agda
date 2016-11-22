
module _ where

open import Issue1278.A Set
open import Agda.Builtin.Equality

test : (c : D) -> (c ≡ c)
test d = {!!} -- goal ".#A-60005532.d ≡ .#A-60005532.d"
