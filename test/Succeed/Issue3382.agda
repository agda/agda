{-# OPTIONS --cubical --rewriting --confluence-check #-}

open import Agda.Primitive.Cubical public

postulate
  Int : Set
  _↦_ : {A : Set} → A → A → Set
  id↦ : {A : Set} {a : A} → a ↦ a

{-# BUILTIN REWRITE _↦_ #-}

postulate
  hcompIntEmpty : (n : Int) → primHComp (λ _ → isOneEmpty) n ↦ n

{-# REWRITE hcompIntEmpty #-}

test : (n : Int) → primHComp (λ _ → isOneEmpty) n ↦ n
test n = id↦
