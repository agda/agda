{-# OPTIONS --irrelevant-projections --erasure #-}

data _≡_ {A : Set} : A → A → Set where
  refl : (x : A) → x ≡ x

module Erased where

  record Erased (A : Set) : Set where
    constructor [_]
    field
      @0 erased : A

  open Erased

  record _↔_ (A B : Set) : Set where
    field
      to      : A → B
      from    : B → A
      to∘from : ∀ x → to (from x) ≡ x
      from∘to : ∀ x → from (to x) ≡ x

  postulate
    A : Set
    P : (B : Set) → (Erased A → B) → Set
    p : (B : Set) (f : Erased A ↔ B) → P B (_↔_.to f)

  fails : P (Erased (Erased A)) (λ (x : Erased A) → [ x ])
  fails =
    p _ (record
           { from    = λ ([ x ]) → [ erased x ]
           ; to∘from = refl
           ; from∘to = λ _ → refl _
           })

module Irrelevant where

  record Irrelevant (A : Set) : Set where
    constructor [_]
    field
      .irr : A

  open Irrelevant

  record _↔_ (A B : Set) : Set where
    field
      to      : A → B
      from    : B → A
      to∘from : ∀ x → to (from x) ≡ x
      from∘to : ∀ x → from (to x) ≡ x

  postulate
    A : Set
    P : (B : Set) → (Irrelevant A → B) → Set
    p : (B : Set) (f : Irrelevant A ↔ B) → P B (_↔_.to f)

  fails : P (Irrelevant (Irrelevant A)) (λ (x : Irrelevant A) → [ x ])
  fails =
    p _ (record
           { from    = λ ([ x ]) → [ irr x ]
           ; to∘from = refl
           ; from∘to = λ _ → refl _
           })
