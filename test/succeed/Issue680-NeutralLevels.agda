-- {-# OPTIONS --verbose tc.conv.term:40 #-}
-- {-# OPTIONS --verbose tc.conv.level:40 #-}
-- {-# OPTIONS --verbose tc.conv.atom:50 #-}
-- {-# OPTIONS --verbose tc.conv.elim:50 #-}

module Issue680-NeutralLevels where

open import Common.Level

postulate N : Set
          A : N → Set
          B : Set
          level' : B → Level
          lac : ∀ {n} → A n → B
          I : Level → Level → Set
          refl : ∀ {l : Level} → I l l
          Top : Set
          top : Top

data Test : Set where
  mkTest : (n : N) → (tel : A n) → Test

test : Test → Top
test (mkTest n tel) = top
  where
    test′ : I (lsuc (level' (lac tel))) (lsuc (level' (lac tel)))
    test′ = refl

