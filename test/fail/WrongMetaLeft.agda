{-# OPTIONS --universe-polymorphism #-}
module WrongMetaLeft where

open import Imports.Level

postulate
  ∃₂ : ∀ {a c : Level} {A : Set a} {B : Set}
         (C : A → B → Set c) → Set (a ⊔ c)
  proj₂ : ∀ {a c}{A : Set a}{B : Set}{C : A → B → Set c} → ∃₂ {a}{c}{A}{B} C → B

postulate
  Position : Set
  Result   : Set
  _≡_      : Result → Result → Set

postulate
  Mono : {p : Level} (P : Position → Position → Set p) → Set p

postulate
  Fun : ∀ {a : Level} {A : Set a} →
          (A → A → Set) → (A → Result) → Set a

-- The problem is that the "wrong" meta is left unsolved. It's really the
-- level of _<P_ that's not getting solved but it's instantiated to the
-- sort of the type of resultsEqual, so the yellow ends up in a weird place.
postulate
  Monad :
    (_<P_ : Position → Position → Set _) →
    (Key : Mono _<P_ -> Result -> Set)
    (_≈_ : ∃₂ Key → ∃₂ Key → Set)
    (resultsEqual : Fun {_} {∃₂ {_}{_}{Mono _<P_}{Result} Key}
                        _≈_ (\(rfk : ∃₂ Key) ->
                            proj₂ {_}{_}{_}{Result}{_} rfk))
    → Set
