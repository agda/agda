-- Andreas, 2020-09-26, issue #4944.
-- Size solver got stuck on projected variables which are left over
-- in some size constraints by the generalization feature.

-- {-# OPTIONS --sized-types #-}
-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.conv.size:60 -v tc.size:30 -v tc.meta.assign:10 #-}

open import Agda.Builtin.Size

variable
  i : Size

postulate
  A : Set

data ListA (i : Size) : Set where
  nil   : ListA i
  cons  : (j : Size< i) (t : A) (as : ListA j) → ListA i

postulate
  node : A → ListA ∞ → A
  R    : (i : Size) (as as′ : ListA i) → Set

  test : -- {i : Size} -- made error vanish
         (t u : A) (as : ListA i) →
         R (↑ (↑ i)) (cons (↑ i) t (cons i u as)) (cons _ (node t (cons _ u nil)) as)

variable
  t u : A
  as : ListA i

postulate
  tst2 : R _ (cons _ t (cons _ u as)) (cons _ (node t (cons _ u nil)) as)

-- Should pass.
