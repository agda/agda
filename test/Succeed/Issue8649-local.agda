{-# OPTIONS --rewriting --local-confluence-check #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite

postulate
  A : Set

record Tree : Set where
  coinductive
  field
    force : A

postulate
  sem : A → Tree

  sem-force :
    {a : A} →
    Tree.force (sem a) ≡ a

{-# REWRITE sem-force #-}

data Rel : Tree → Set where
  state :
    {a : A} →
    Rel (sem a)

step :
  ∀ {X : Tree} →
  Rel X →
  Tree.force X ≡ Tree.force X
step state =
  refl
