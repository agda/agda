--------------------------------------------------------------------------------
-- Prelude

data ⊥ : Set where

-- Unit sans eta
data ⊤ : Set where
  tt : ⊤

⊤-rec : ∀ {ℓ} {A : Set ℓ} → ⊤ → A → A
⊤-rec tt x = x

--------------------------------------------------------------------------------
-- False

Negate : (x : ⊤) → ⊤-rec x (Set → Set)
Negate tt X = (X → ⊥)

mutual
  -- This tricks the positivity checker, which doesn't add
  -- an edge from the second argument of P to Negate.
  P : (x : ⊤) → ⊤-rec x (Set → Set)
  P = Negate

  -- This in turn breaks positivity checking for FixP
  data FixP : Set where
    wrap : P tt FixP → FixP

no-fixp : FixP → ⊥
no-fixp (wrap x) = x (wrap x)

yet-fixp : FixP
yet-fixp = wrap no-fixp

bang : ⊥
bang = no-fixp yet-fixp
