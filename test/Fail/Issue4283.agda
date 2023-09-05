-- Hot fix (Jesper, 2019-12-14)of de Bruijn issue in
-- https://github.com/agda/agda/commit/a30c7be25a3085246154f41cbb472119e229b580
-- "Replace one use of inTopContext with unsafeInTopContext"
-- "TODO: find the fundamental cause and switch back to inTopContext"

open import Agda.Primitive

postulate Id : (l : Level) (A : Set l) → A → A → Set l

postulate w/e : (l : Level) (A : Set l) → A

data Box l (A : Set l) : Set l where
  box : A → Box l A

unbox : (l : Level) (A : Set l) → Box l A → A
unbox l A (box x) = x

record R l (A : Set l) : Set l where
  --no-eta-equality
  -- ^ works if eta is disabled
  field
    boxed : Box l A
    refl  : Id l A (w/e l A) (w/e l A)

postulate
  El    : (l : Level) (A : Set l) → A → A
  trans : (l : Level) (A : Set l) (x : A) → Id l A (w/e l A) (w/e l A) → Id l A (w/e l A) (w/e l A) → Id l A (w/e l A) (w/e l A)
  cong  : (l : Level) (A : Set l) (f : A → A) (x y : A) → Id l A x y → Id l A (f x) (f y)

module _ (l : Level) (BADNESS : Set) (A : Set l) (r : R l A) where

  open R r

  x = w/e l A

  p = trans l A (unbox l A boxed) refl refl

  lemma = El l
            (Id l (Id l A x x) p p)
            (cong l _ (λ p → trans l A (unbox l A boxed) p _) refl refl (w/e l (Id l (Id l A x x) refl refl)))
  -- ^ works if definition of lemma is removed

  test = λ _ → unbox _ _ boxed

-- Expected error:
--
-- Failed to solve the following constraints:
--   _43 (p = refl) = refl : Id l A (w/e l A) (w/e l A) (blocked on _43)
