-- This variant of the code is due to Ulf Norell.

{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Size

data ⊥ : Set where

mutual

  data Unit (i : Size) : Set where
    c : Unit′ i → Unit i

  data Unit₁ (i : Size) : Set where
    c₁ : ⊥ → Unit i → Unit₁ i

  record Unit′ (i : Size) : Set where
    coinductive
    field
      force : {j : Size< i} → Unit₁ j

open Unit′ public

tail : Unit ∞ → Unit₁ ∞
tail (c x) = force x

u : (∀ {i} → Unit′ i → Unit i) →
    ∀ {i} → Unit₁ i
u cons = tail (cons λ { .force → u cons })

bad : Unit₁ ∞
bad = u c

refute : Unit₁ ∞ → ⊥
refute (c₁ () _)

loop : ⊥
loop = refute bad
