-- It seems as if our fix for singleton records was not good enough;
-- the following code was accepted by Agda 2.2.6.
-- Fixed now.
module Issue245 where

record ⊤ : Set where

postulate
  A : Set
  x : A

record R₁ (P : A → Set) : Set where
  field
    f : P x

record R₂ : Set₁ where
  field
    F : A → Set
    f : R₁ F

record R₃ (R : R₂) : Set where
  field
    f : A

R : R₂
R = record
  { F = λ (x : A) → ⊤
  ; f = record {}
  }

foo : R₃ R → A
foo = R₃.f {_}

-- No unsolved metas at the following locations:
--   /home/nad/research/dtp/lib/Bug.agda:32,13-14

