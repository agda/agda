{-# OPTIONS --rewriting #-}

-- {-# OPTIONS -v rewriting:30 #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality renaming (_≡_ to _≡≡_)

record Eq (t : Set) : Set₁ where
  field
    _≡_ : t → t → Set

open Eq {{...}}

{-# BUILTIN REWRITE _≡_ #-}

instance
  eqN : Eq Nat
  eqN = record { _≡_ = _≡≡_ }

postulate
  plus0p :  ∀{x} → (x + zero) ≡ x

{-# REWRITE plus0p #-}

-- Warning:
-- plus0p  does not target rewrite relation
-- when checking the pragma REWRITE plus0p

-- The type of the postulate ends in _≡≡_ (after reduction)
-- but the rewrite relation is _≡_
