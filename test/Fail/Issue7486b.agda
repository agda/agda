data D : Set where
  con : D

record R : Set where
  no-eta-equality -- no error if eta-equality
  field proj : D

F : (D → Set) → D → Set -- no error if F : Set → D → Set
F k con = k con         -- no error if F k con = D

postulate
  instance i : {r : R} → F (λ _ → D) (R.proj r)

postulate
  A : Set
  instance a : A

it : {{A}} → A
it {{x}} = x

-- Larger version of Issue7486.

x : A
x = it

{-
Failed to solve the following constraints:
  Resolve instance argument _11 : A
  Candidates
    i : {r : R} → F (λ _ → D) (R.proj r)
    a : A
    (stuck)
-}
