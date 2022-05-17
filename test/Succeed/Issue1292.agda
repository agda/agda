-- Andreas, 2014-10-05, issue reported by Stevan Andjelkovic

{-# OPTIONS --cubical-compatible #-}

postulate
  IO : Set → Set

record ⊤ : Set where
  constructor tt

record Container : Set₁ where
  field
    Shape    : Set
    Position : Shape → Set

open Container public

data W (A : Set) (B : A → Set) : Set where
  sup : (x : A) (f : B x → W A B) → W A B

postulate
  Ω : Container
  p : ∀ {s} → Position Ω s

mutual
  bad : W (Shape Ω) (Position Ω) → IO ⊤
  bad (sup c k) = helper c k

  helper : (s : Shape Ω) → (Position Ω s → W (Shape Ω) (Position Ω)) → IO ⊤
  helper _ k = bad (k p)

-- should pass termination check
