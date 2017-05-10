-- Andreas, 2017-02-14 issue #2455 reported by mechvel
-- Test case by Andrea

-- Seem that the fix for issue #44 was not complete.

-- When inserting module parameters for a definition,
-- we need to respect polarities!

-- Jesper, 2017-05-10 temporarily moved to Fail

-- {-# OPTIONS -v tc.decl:10 -v tc.polarity:70 -v tc.sig.inst:30 #-}

module Issue2455 where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data Unit : Set where
  unit : Unit

postulate
  A : Set
  P : A → Set
  p : ∀ {e} → P e

module M (e : A) (f : Unit) where

   aux : Unit → P e
   aux unit = p

   -- se does not depent on f
   -- se gets type (e : A) (f :{UnusedArg} Unit) -> A
   se = e

   -- aux' should not depend on f
   -- For this to work, the module parameters for se must be
   -- respecting UnusedArg.
   aux' : Unit → P se
   aux' unit = p

works : ∀ x y e → M.aux e x ≡ M.aux e y
works _ _ _ = refl

fails : ∀ x y e → M.aux' e x ≡ M.aux' e y
fails _ _ _ = refl
