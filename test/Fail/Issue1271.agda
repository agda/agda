-- Andreas, issue reported by Matteo Acerbi, 2014-09-04.
-- Short summary: x = c x is not impossible for coinductive constructors c,
-- so x should not be considered a strictly rigid occurrence in (c x).

-- Matteo:

-- In the following I cannot understand what justifies the absurd pattern
-- in the definition of ¬id≡In: as νId is coinductive, elaboration of the
-- no-cycles check to eliminators should not be possible (as far as I know).

-- Any two inhabitants of νId are bisimilar, but it seems that current
-- pattern matching makes it inconsistent to assume that bisimilarity
-- implies equality for νId, which *might* upset some. :-)

{-# OPTIONS --guardedness #-}

-- False and equality.

⊥ = (X : Set) → X

data _≡_ {A : Set}(x : A) : A → Set where
  <> : x ≡ x

-- The cofixpoint of the identity functor.

record νId : Set where
  coinductive
  constructor In
  field       Out : νId
open νId

-- The "only" inhabitant of νId.

tt : νId
Out tt = tt

-- x ≡ In x is considered absurd.

¬id≡In : {x : νId} → x ≡ In x → ⊥
¬id≡In ()

-- _≈_ is bisimilarity for elements of νId.

record _≈νId_ (x y : νId) : Set where
  coinductive
  field step : Out x ≈νId Out y
open _≈νId_

-- Any two elements are bisimilar.

trivial-≈νId : ∀ {x y} → x ≈νId y
step trivial-≈νId = trivial-≈νId

-- For νId it is not consistent to assume that bisimilarity implies
-- equality.

problem? : (ext : ∀ {x y} → x ≈νId y → x ≡ y) → ⊥
problem? ext = ¬id≡In {tt} (ext trivial-≈νId)
