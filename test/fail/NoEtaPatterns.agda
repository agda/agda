
record _×_ (A B : Set) : Set where
  no-eta-equality
  constructor _,_
  field
    fst : A
    snd : B

open _×_

swap : ∀ {A B} → A × B → B × A
swap (x , y) = y , x

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- This should fail since we don't have eta for _×_.
fails : ∀ {A B} (p : A × B) → swap p ≡ (snd p , fst p)
fails p = refl
