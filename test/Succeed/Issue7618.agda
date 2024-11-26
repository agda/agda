{-# OPTIONS --rewriting --allow-unsolved-metas #-}
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  eq : (A B : Set) → Bool
  eq-id : (A : Set) → eq A A ≡ true
  {-# REWRITE eq-id #-}

postulate
  A B : Set
  f : (r : Set → Set) (P : (Set → Bool) → Set) → P (λ _ → eq (r A) (r B))

g : (r : Set → Set) (P : (Set → Bool) → Set) → P (λ _ → eq (r A) (r B))
g r P = f r _     -- WAS: internal error
