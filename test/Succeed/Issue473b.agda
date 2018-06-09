-- Andreas, Ulf, 2015-06-03
-- Issue 473 was not fixed for records without constructor
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _×_

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Zero : Nat → Set where
  zero : Zero zero

data Zero₂ : Nat → Nat → Set where
  zero : Zero₂ zero zero

f₁ : (p : Nat × Nat) → Zero₂ (fst p) (snd p) → Set
f₁ (.zero , .zero) zero = Nat    -- works
-- f₁ .(zero , zero) zero = Nat  -- fails

f₂ : (p : Nat × Nat) → Zero (fst p) → Set
f₂ (.zero , y) zero = Nat  -- works
-- foo .?? zero             -- fails (nothing to write in place of ??)

f₃ : {p : Nat × Nat} → Zero (fst p) → Set
f₃ zero = Nat

f₄ : {p : Nat × (Nat × Nat)} → Zero (fst (snd p)) → Set
f₄ zero = Nat

f₅ : {p : Nat × Nat} → Zero₂ (fst p) (snd p) → Set
f₅ zero = Nat

data I : Set where
  i : I

record Box (A B : Set) : Set where
  -- no constructor [_]
  field contents : A

[_] : ∀{A B} → A → Box A B
[ a ] = record { contents = a }

data D : Set → Set₁ where
  d₁ : (R : Set) → D R
  d₂ : (i : I) (R : I → Set) → D (R i) → D (Box I (R i))

data S : (R : Set) → R → D R → Set₁ where
  s : (j : I) (R : I → Set) (p : D (R j)) →
      S (Box I (R j)) [ j ] (d₂ j R p)

postulate
  P : I → Set

Fails : {e : Box I (P i)} → S (Box I (P i)) e (d₂ i P (d₁ (P i))) → Set₁
Fails (s .i .P .(d₁ (P i))) = Set

-- Refuse to solve heterogeneous constraint p : D (P (Box.contents e))
-- =?= d₁ (P i) : D (P i)
-- when checking that the pattern s .i .P .(d₁ (P i)) has type
-- S (Box I (P i)) e (d₂ i P (d₁ (P i)))
