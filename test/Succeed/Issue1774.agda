-- 2016-01-14 Andreas, issue reported by Martin Stone Davis

open import Common.Equality

module _ {K : Set} where

record Map : Set where
  field
    unmap : K

record _∉_ (k : K) (m : Map) : Set where
  field
    un∉ : Map.unmap m ≡ k

pattern ∉∅ = record { un∉ = refl }

not-here : ∀ {k : K} {m : Map} (k∉m : k ∉ m) → Set
not-here ∉∅ = K

-- WAS: internal error due to record pattern not yet treated
-- for pattern synonyms.
