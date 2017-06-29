open import Common.Bool
open import Common.Nat

data cheesy : Bool → Set where
  chocolate : cheesy false
  cheese    : cheesy true
  bread     : ∀ x → cheesy x

foo : ∀ {x : Bool} → cheesy x → cheesy x → Bool
foo x chocolate = {!!}
foo x cheese = {!!}
foo x (bread false) = {!x!}
foo x (bread true) = {!!}
