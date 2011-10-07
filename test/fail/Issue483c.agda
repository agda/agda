
module Issue483c where

data _≡_ {A : Set}(a : A) : A → Set where
 refl : a ≡ a

data ⊥ : Set where
record ⊤ : Set where

refute : .⊥ → ⊥
refute ()

mk⊤ : ⊥ → ⊤
mk⊤ ()

X   : .⊤ → ⊥
bad : .(x : ⊥) → X (mk⊤ x) ≡ refute x
X     = _
bad x = refl

false : ⊥
false = X _
