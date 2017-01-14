-- Andreas, 2017-01-14, issue #2405 reported by m0davis
-- Instance not found due to regression introduced by
-- parameter-refinement.

-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.instance:70 #-}
-- {-# OPTIONS -v tc.meta.assign:40 #-}
-- {-# OPTIONS -v tc.conv:40 #-}
-- {-# OPTIONS -v tc.sig.param:100 #-}

postulate
  R : Set → Set
  S : (F : Set → Set) ⦃ _ : {A : Set} → R (F A) ⦄ → Set

module M1 (X : Set) where
  postulate
    F : Set → Set
    instance Ri : {A : Set} → R (F A)
    Si-works : S F ⦃ Ri ⦄
    Si-test  : S F

-- WAS:
-- No instance of type R (F A) was found in scope. -}
--
-- candidate:
--   Ri X    : (A : Set) → R (F X A)
--   Ri 0    : Π Set λ A → R (F 1 0)
--   Ri 0 _A : R (F 0 (_A 1 0))
-- goal:
--   getMetaType
--   ? : (X A : Set) → R (F X A)
--   ? : Π Set λ X → Pi Set λ A → R (F 1 0)
--   ? : R (F A)
--   ? : R (F 1 0)

-- Should succeed.
