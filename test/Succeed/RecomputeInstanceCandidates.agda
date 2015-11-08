
record ⊤ : Set where
  instance constructor tt

data ⊥ : Set where

data Inf : Set where
  -∞ ∞ : Inf

Less : Inf → Inf → Set
Less ∞ _ = ⊥
Less _ ∞ = ⊤
Less _ _ = ⊥

data Bounded : Inf → Set where
  bound : ∀ {b} {{lt : Less -∞ b}} → Bounded b

-- The first time around the target type is Less -∞ _b which results in no
-- candidates. Once _b gets solved candidates need to be recomputed.
foo : Bounded ∞
foo = bound
