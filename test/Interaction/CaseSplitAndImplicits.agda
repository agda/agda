{-# OPTIONS --no-keep-pattern-variables #-}

open import Agda.Builtin.Equality

-- Case splitting should not remove implicit arguments
record ⊤ : Set where constructor tt

test₁ : {A : Set} → ⊤ → ⊤
test₁ {A} x = {!x!}

-- Case splitting on an implicit argument should make it visible
test₂ : {x : ⊤} → ⊤
test₂ = {!x!}

-- Implicit variables in dot patterns should be replaced by _
postulate
  A B : Set
  f : A → B

test₃ : {x : A} (y : B) → f x ≡ y → B
test₃ y e = {!e!}

-- .. but not if they are bound inside the dot pattern
test₄ : (f : A → A) → f ≡ (λ x → x) → Set
test₄ f e = {!e!}
