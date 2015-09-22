module Issue690a where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- A negative type.
data T : Set → Set where
  c : T (T ℕ)

-- From Andreas (2012-09-07) message on Agda mailing list "Forget
-- Hurken's paradox ..."
--
-- Trying to make sense of T in terms of inductive types, explaining
-- indices via equalities, one arrives at
--
--  data T (X : Set) : Set where
--    c : (X ≡ T ℕ) → T X
--
-- which has a non-positive occurrence of T in (X ≡ T ℕ).
--
-- An argument for the existence of T would have to argue for the
-- existence this least fixed point:
--
--  lfp \lambda T X → (X ≡ T ℕ)


-- ASR (14 August 2014): In Coq'Art, § 14.1.2.1, the type T is
-- rejected due to the head type constrains.
