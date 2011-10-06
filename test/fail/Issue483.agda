-- We need to look at irrelevant variables in meta instantiation occurs check.
-- Here's why.
module Issue483 where

data _==_ {A : Set}(x : A) : A → Set where
  refl : x == x

data ⊥ : Set where

resurrect : .⊥ → ⊥
resurrect ()

data D : Set where
  c : (x : ⊥) → (.(y : ⊥) → x == resurrect y) → D

d : D
d = c _ (λ y → refl)
-- this should leave an unsolved meta!  An error is too harsh.
{-
-- Cannot instantiate the metavariable _21 to resurrect _ since it
-- contains the variable y which is not in scope of the metavariable
-- when checking that the expression refl has type _21 == resurrect _
-}

¬d : D → ⊥
¬d (c x _) = x

oops : ⊥
oops = ¬d d
