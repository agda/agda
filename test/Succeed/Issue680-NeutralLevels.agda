-- {-# OPTIONS -v tc.meta:40 #-}
-- {-# OPTIONS --verbose tc.conv.term:40 #-}
-- {-# OPTIONS --verbose tc.conv.level:40 #-}
-- {-# OPTIONS --verbose tc.conv.atom:50 #-}
-- {-# OPTIONS --verbose tc.conv.elim:50 #-}

module Issue680-NeutralLevels where

open import Common.Level

postulate
  N     : Set
  A     : N → Set
  level : N → Level
  lac   : ∀ {n} → A n → N
  I     : Level → Level → Set
  refl  : ∀ {l : Level} → I l l

data Test : Set where
  mkTest : (n : N) → (tel : A n) → Test

test : Test → N
test (mkTest n tel) = n
  where
    test′ : I (lsuc (level (lac tel)))
              (lsuc (level (lac tel)))
    test′ = refl

