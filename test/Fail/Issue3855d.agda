{-# OPTIONS --erasure #-}

open import Agda.Builtin.Equality

record _↠_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    to∘from : ∀ x → to (from x) ≡ x

record Erased (@0 A : Set) : Set where
  constructor [_]
  field
    @0 erased : A

open Erased

-- fails : {A : Set} → A ↠ Erased A
-- fails = record
--   { to      = [_]
--   ; from    = erased
--   ; to∘from = λ _ → refl
--   }

works : {A : Set} → A ↠ Erased A
works = record
  { to      = [_]
  ; from    = _
  ; to∘from = λ _ → refl
  }
