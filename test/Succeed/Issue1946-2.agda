-- A minor variant of code reported by Andreas Abel. The code below
-- should be rejected.

open import Agda.Builtin.Size

data ⊥ : Set where

data SizeLt (i : Size) : Set where
  size : (j : Size< i) → SizeLt i

data D {i : Size} : SizeLt i → Set where
  c : ∀{i' : Size< i} → ((j : SizeLt i') → D j) → D (size i')

f : D (size ∞) → ⊥
f (c h) = f (h (size ∞))

d : ∀{i} s → D {i} s
d (size i) = c λ{ (size j) → d (size j) }

loop : ⊥
loop = f (d (size ∞))
