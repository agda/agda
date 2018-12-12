-- Andreas, 2015-05-02 Integrate copatterns with with.

{-# OPTIONS --guardedness #-}

open import Common.Prelude hiding (map)
open import Common.Product
open import Common.Equality

dup : {A : Set} → A → A × A
proj₁ (dup a) = a
proj₂ (dup a) with a
proj₂ (dup a) | x = x

record Stream (A : Set) : Set where
  coinductive
  constructor delay
  field
    force : A × Stream A
open Stream

map : ∀{A B} → (A → B) → Stream A → Stream B
force (map f s) with force s
... | a , as = f a , map f as

zipWith : ∀{A B C} → (A → B → C) → Stream A → Stream B → Stream C
force (zipWith f s t) with force s | force t
... | a , as | b , bs = f a b , zipWith f as bs

interleave : ∀{A} (s t : Stream A) → Stream A
force (interleave s t) with force s
... | a , as = a , interleave t as

mutual
  evens : ∀{A} (s : Stream A) → Stream A
  force (evens s) with force s
  ... | a , as = a , odds as

  odds : ∀{A} (s : Stream A) → Stream A
  odds s with force s
  ... | a , as = evens as

take : ∀{A} (n : Nat) (s : Stream A) → List A
take 0       s = []
take (suc n) s with force s
... | a , as = a ∷ take n as


record Bisim {A B} (R : A → B → Set) (s : Stream A) (t : Stream B) : Set where
  coinductive
  constructor ~delay
  field
    ~force : let a , as = force s
                 b , bs = force t
             in  R a b × Bisim R as bs
open Bisim

SEq : ∀{A} (s t : Stream A) → Set
SEq = Bisim (_≡_)

~refl : ∀{A} (s : Stream A) → SEq s s
~force (~refl s) with force s
... | a , as = refl , ~refl as

~sym : ∀{A}{s t : Stream A} → SEq s t → SEq t s
~force (~sym p) with ~force p
... | q , r = sym q , ~sym r

~sym' : ∀{A} {s t : Stream A} → SEq s t → SEq t s
~force (~sym' {s = s} {t} p) with force s | force t | ~force p
... | a , as | b , bs | r , q rewrite r = refl , ~sym' q

-- ~sym' : ∀{A} {s t : Stream A} → SEq s t → SEq t s
-- ~force (~sym' {s = s} {t} p) with force s | force t | ~force p
-- ... | x | y | q , r = {!x!} -- C-c C-c prints internal with-name

~trans : ∀{A}{r s t : Stream A} → SEq r s → SEq s t → SEq r t
~force (~trans p q) with ~force p | ~force q
... | ph , pt | qh , qt = trans ph qh , ~trans pt qt

~take : ∀{A} (s t : Stream A) (p : SEq s t) (n : Nat) → take n s ≡ take n t
~take s t p zero = refl
~take s t p (suc n) with force s | force t | ~force p
~take s t p (suc n) | a , as | .a , bs | refl , q rewrite ~take as bs q n = refl
