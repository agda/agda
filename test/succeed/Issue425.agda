{- Reported by Nils Anders Danielsson, 2011-07-06

From the release notes for Agda 2.2.10:

  "Projections now preserve sizes, both in patterns and expressions."

However, the following code is rejected:
-}

module Issue425 where

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_

id : {A : Set} → A → A
id x = x

data I : Set where
  c : I → I → I

data D : I → Set where
  d : (j : I × I)  → D (proj₁ j) → D (proj₂ j) → D (c (proj₁ j) (proj₂ j))

f : ∀ i → D i → Set
f .(c (proj₁ j) (proj₂ j)) (d j l r) = f (proj₁ j) (id l)

{- Is this intentional? I guess the issue here is the subterm relation
rather than the sizes. Should we modify the subterm relation?
-}
-- Andreas, 2011-07-07 this should termination check.
