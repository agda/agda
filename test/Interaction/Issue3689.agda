-- Andreas, 2019-04-10, issue #3689, reported by andrejtokarcik

-- Regression introduced by #3533 (dropping trivially impossible clauses
-- during case-splitting).

-- {-# OPTIONS -v interaction.case:100 #-}
-- {-# OPTIONS -v tc.cover:100 #-}

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

record R (A : Set) : Set where
  field π : A

fun : {A : Set} (xyz : Σ (R A) λ r → Σ (R.π r ≡ R.π r) λ _ → R.π r ≡ R.π r) → Set
fun (x , y) = {!y !} -- C-c C-c

-- WAS: internal error.

-- Should succeed.
