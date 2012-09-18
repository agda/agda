-- There was a bug when unifying things of function type during pattern matching
-- (the T argument to P is unified with D below)
module Issue199 where

data D (A : Set) : Set where

data P {A : Set} : {T : Set → Set} → T A → Set where
 p : ∀ d → P {_} {D} d

foo : ∀ {A} {l : D A} → P l → Set₁
foo (p _) = Set
