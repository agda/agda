{-# OPTIONS --copatterns --sized-types #-}
-- {-# OPTIONS -v tc.size.solve:60 #-}

open import Common.Size
open import Common.Prelude
open import Common.Product

-- Sized streams via head/tail.

record Stream {i : Size} (A : Set) : Set where
  coinductive
  constructor delay
  field
    force : ∀ {j : Size< i} → A × Stream {j} A
open Stream public

_∷ˢ_ : ∀{i A} → A → Stream {i} A → Stream {↑ i} A
force (a ∷ˢ s) = a , s

-- Prepending a list to a stream.

_++ˢ_ : ∀ {i A} → List A → Stream {i} A → Stream {i} A
(a ∷ as) ++ˢ s = a ∷ˢ (as ++ˢ s)
[]       ++ˢ s = s
