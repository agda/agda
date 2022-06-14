-- Andreas, 2022-06-14, issue #5953 reported by Szumi Xi
-- Cubical Agda switches dot-pattern termination off (#4606).
-- However, this breaks also some benign cases.
--
-- In this example with inductive-inductive types,
-- dotted variables should still be recognized
-- as variable patterns for termination certification.

{-# OPTIONS --cubical #-}  -- worked with --without-K but not --cubical

-- Debugging:
-- {-# OPTIONS -v term.check.clause:25 #-}
-- {-# OPTIONS -v term:20 #-}

data Con : Set
data Ty : Con → Set

data Con where
  nil : Con
  ext : (Γ : Con) → Ty Γ → Con

data Ty where
  univ : (Γ : Con) → Ty Γ
  pi : (Γ : Con) (A : Ty Γ) → Ty (ext Γ A) → Ty Γ

module _
  (A : Set)
  (B : A → Set)
  (n : A)
  (e : (a : A) → B a → A)
  (u : (a : A) → B a)
  (p : (a : A) (b : B a) → B (e a b) → B a)
  where
  recCon : Con → A
  recTy : (Γ : Con) → Ty Γ → B (recCon Γ)

  recCon nil = n
  recCon (ext Γ A) = e (recCon Γ) (recTy Γ A)

  recTy Γ (univ Γ) = u (recCon Γ)
  recTy Γ (pi Γ A B) = p (recCon Γ) (recTy Γ A) (recTy (ext Γ A) B)

-- Should pass the termination checker.
