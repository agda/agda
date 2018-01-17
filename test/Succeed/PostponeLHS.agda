
-- Check that checking of left-hand sides are postponed properly
-- when the type of an argument that is matched on is a meta.

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data X : Set where
  zero : X

-- TODO: uncomment below once LHS postponing is actually implemented
-- Jesper, 2017-11-16: is this really what we want?

-- easy : _ → Nat
-- easy (suc n) = n
-- easy zero    = zero

-- hard : _ → Nat
-- hard zero    = zero
-- hard (suc n) = hard n

-- _$_ : {A B : Set} → (A → B) → A → B
-- f $ x = f x

-- plam : Nat
-- plam = (λ { zero → zero; (suc n) → n }) $ suc zero
