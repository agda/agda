{- Reported by Nils Anders Danielsson, 2011-07-06

From the release notes for Agda 2.2.10:

  "Projections now preserve sizes, both in patterns and expressions."

However, the following code is rejected:
-}

module SubTermAndProjections where

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_

postulate
 i : {A : Set} → A → A

data I : Set where
  c1 : I → I
  c2 : I → I → I

data D : I → Set where
  d : (j : I × I)  → D (c1 (proj₁ j)) → D (proj₂ j) → D (c2 (c1 (proj₁ j)) (proj₂ j))

f : ∀ i → D i → Set
f .(c2 (c1 (proj₁ j)) (proj₂ j)) (d j l r) = f (c1 (proj₁ j)) (i l)

{- Is this intentional? I guess the issue here is the subterm relation
rather than the sizes. Should we modify the subterm relation?
-}
-- Andreas, 2011-07-07 this should termination check.
