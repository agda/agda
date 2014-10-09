module Issue1296.SolvedMeta where

open import Common.Prelude
open import Common.Equality

test : zero ≡ {!!}
test = refl
