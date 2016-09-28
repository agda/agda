-- Andreas, 2016-09-28
-- Level constraints X <= a and a <= X should solve X = a.

-- {-# OPTIONS -v tc.constr.add:40 #-}

open import Common.Level

module _ (a : Level) where
 mutual
  X : Level
  X = _

  data C : Set (lsuc X) where
    c : Set a → C  -- constrains X by a <= X

  data D : Set (lsuc a) where
    c : Set X → D  -- constrains X by X <= a

-- should succeed
