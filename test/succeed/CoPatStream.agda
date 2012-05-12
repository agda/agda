{-# OPTIONS --copatterns #-}
-- {-# OPTIONS --no-positivity-check #-}
-- {-# OPTIONS -v tc.def.fun:50  #-}
-- {-# OPTIONS -v 100  #-}
module CoPatStream where

open import Common.Equality

record Stream (A : Set) : Set where
  field
    head : A
    tail : Stream A
module S = Stream

record _≈_ {A : Set}(s t : Stream A) : Set where
  field
    head : S.head s ≡ S.head t
    tail : S.tail s ≈ S.tail t
module B = _≈_

module CoPat where

  {-# NO_TERMINATION_CHECK #-}
  map : {A B : Set} → (A → B) → Stream A → Stream B
  S.head (map f s) = f (S.head s)
  S.tail (map f s) = map f (S.tail s)

  {-# NO_TERMINATION_CHECK #-}
  map_id : {A : Set}(s : Stream A) → map (λ x → x) s ≈ s
  B.head (map_id s) = refl
  B.tail (map_id s) = map_id (S.tail s)

module HandTranslated where

  {-# NO_TERMINATION_CHECK #-}
  map : {A B : Set} → (A → B) → Stream A → Stream B
  map f s = record
    { head = f (S.head s)
    ; tail = map f (S.tail s)
    }

  {- loops
  {-# NO_TERMINATION_CHECK #-}
  map_id : {A : Set}(s : Stream A) → map (λ x → x) s ≈ s
  map_id s = record
    { head = refl
    ; tail = map_id (S.tail s)
    }
  -}
