
module Issue473 where

record _×_ A B : Set where
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
  constructor [_]
  field contents : A

data D : Set → Set₁ where
  d₁ : (R : Set) → D R
  d₂ : (i : I) (R : I → Set) → D (R i) → D (Box I (R i))

data S : (R : Set) → R → D R → Set₁ where
  s : (j : I) (R : I → Set) (p : D (R j)) →
      S (Box I (R j)) [ j ] (d₂ j R p)

postulate
  P : I → Set

WorksNow : {e : Box I (P i)} → S (Box I (P i)) e (d₂ i P (d₁ (P i))) → Set₁
WorksNow (s .i .P .(d₁ (P i))) = Set

-- No constructor
record Pair A B : Set where
  field
    first  : A
    second : B

open Pair

postulate
  T : {A B : Set} → A → B → Set
  mkT : ∀ {A B} (x : A)(y : B) → T x y

-- p is expanded even though it has no named constructor
bar : ∀ {A B} {p : Pair A B} → T (first p) (second p)
bar = mkT _ _
