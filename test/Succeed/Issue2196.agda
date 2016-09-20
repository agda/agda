-- Andreas, 2016-09-20, issue #2196 reported by mechvel
-- Test case by Ulf

-- {-# OPTIONS -v tc.lhs.dot:40 #-}

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

record _×_ (A B : Set) : Set where
  constructor _,_
  field fst : A
        snd : B
open _×_

EqP₁ : ∀ {A B} (p q : A × B) → Set
EqP₁ (x , y) (z , w) = (x ≡ z) × (y ≡ w)

EqP₂ : ∀ {A B} (p q : A × B) → Set
EqP₂ p q = (fst p ≡ fst q) × (snd p ≡ snd q)

works : {A : Set} (p q : A × A) → EqP₁ p q → Set₁
works (x , y) .(x , y) (refl , refl) = Set

test  : {A : Set} (p q : A × A) → EqP₂ p q → Set₁
test  (x , y) .(x , y) (refl , refl) = Set

-- ERROR WAS:
-- Failed to infer the value of dotted pattern
-- when checking that the pattern .(x , y) has type .A × .A
