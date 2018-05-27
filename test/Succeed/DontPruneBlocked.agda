-- {-# OPTIONS -v tc.meta:25 #-}
-- Andreas, 2013-05-23
module DontPruneBlocked where

open import Common.Equality
open import Common.Product

data Bool : Set where
  true false : Bool

if : {A : Set} → Bool → A → A → A
if true  a b = a
if false a b = b

test1 :
  let Fst : Bool → Bool → Bool
      Fst = _
      I : Bool → Bool
      I = _
  in  (a b : Bool) →
       (if (Fst true false) (Fst a b) (Fst b a) ≡ I a) ×  -- don't prune b from Fst!
       (a ≡ I a) ×
       (Fst a b ≡ a)
test1 a b = refl , refl , refl

test : (A : Set) →
  let X : Bool
      X = _
      Fst : A → A → A
      Fst = _
      Snd : A → A → A
      Snd = _
      I : A → A
      I = _
  in  (a b : A) →
       (if X (Fst a b) (Snd a b) ≡ I a) ×  -- don't prune a from Fst and Snd!
       (if X (Snd a b) (Fst a b) ≡ I b) ×  -- don't prune b from Fst and Snd!
       (a ≡ I a) ×
       (X ≡ true)
test A a b = refl , refl , refl , refl

-- Expected result: unsolved metas
--
-- (unless someone implemented unification that produces definitions by case).
--
-- The test case should prevent overzealous pruning:
-- If the first equation pruned away the b, then the second
-- would have an unbound rhs.
