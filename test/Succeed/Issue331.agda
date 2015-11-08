-- 2010-10-15

module Issue331 where

record ⊤ : Set where
  constructor tt

data Wrap (I : Set) : Set where
  wrap : I → Wrap I

data B (I : Set) : Wrap I → Set₁ where
  b₁ : ∀ i → B I (wrap i)
  b₂ : {w : Wrap I} → B I w → B I w
  b₃ : (X : Set){w : Wrap I}(f : X → B I w) → B I w

ok : B ⊤ (wrap tt)
ok = b₂ (b₁ _)

-- Issue 331 was: Unsolved meta: _45 : ⊤
bad : Set → B ⊤ (wrap tt)
bad X = b₃ X λ x → b₁ _

