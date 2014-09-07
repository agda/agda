-- Andreas, 2014-09-07
open import Common.Equality

data ⊥ : Set where
record ⊤ : Set where

-- Agda allows us to prove that A ≠ (A → B)
test : {A B : Set} → A ≡ (A → B) → ⊥
test ()

-- Agda allows us to prove that A ≠ (B → A)
test' : {A B : Set} → A ≡ (B → A) → ⊥
test' ()

-- But ⊤ is isomorphic to ⊤ → ⊤, which under univalence
-- isomorphism-as-equality contradicts both test and test'.

test'' : (⊤ ≡ (⊤ → ⊤)) → ⊥
test'' = test'

there : ⊤ → (⊤ → ⊤)
there _ _ = _

back : (⊤ → ⊤) → ⊤
back _ = _
