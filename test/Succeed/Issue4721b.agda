{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Equality.Rewrite

postulate
  cast : (A B : Set) → A → B
  cast-rew : (A : Set) (x : A) → cast A A x ≡ x
{-# REWRITE cast-rew #-}

postulate
  A : Set
  x y : A

data D (B : A → Set) (b : B y) : Set where
  con : cast (B x) (B y) ? ≡ b → D B b

record R (B : A → Set) (b : B y) : Set where
  field
    eq : cast (B x) (B y) ? ≡ b
