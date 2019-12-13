{-# OPTIONS --rewriting --confluence-check --double-check #-}

data _==_ {A : Set} : (x y : A) → Set where
  refl : {a : A} → a == a
{-# BUILTIN REWRITE _==_ #-}

postulate
  copy : ∀ {X : Set} → X → X
  A : Set
  a : A
  uip : (p : a == a) → p == refl

record S : Set where
  field
    x : A
    x-β : x == a
open S

module T (s : S) where
  dummy = x-β (copy s)
  {-# REWRITE dummy #-}

  y-β-is-refl : x-β (copy s) == refl
  y-β-is-refl = uip _ -- WAS: Double check complains about solution to meta.
