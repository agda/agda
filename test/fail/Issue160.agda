
module Issue160 where

data Bool : Set where
  true  : Bool
  false : Bool

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

inj : ∀ {A} (f : A -> A) {a b : A} →
      f a ≡ f b -> a ≡ b
inj f refl = refl

absurd : true ≡ false
absurd = inj (λ _ → true) refl
