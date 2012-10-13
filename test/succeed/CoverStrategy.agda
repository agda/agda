-- {-# OPTIONS -v tc.cc:12 -v tc.cover.splittree:10 #-}
-- {-# OPTIONS -v tc.cover.strategy:100 -v tc.cover.precomputed:100 #-}
-- {-# OPTIONS -v tc.cover.split.con:20 #-}
module CoverStrategy where

import Common.Level
open import Common.Prelude renaming (Nat to ℕ)

data _∼_ : ℕ → ℕ → Set where
  pr : ∀ {n} → suc n ∼ n
  eq : ∀ {n} →     n ∼ n

max : ∀ {m n} → m ∼ n → ℕ
max (pr {n}) = suc n
max (eq {n}) =     n

data Tree : ℕ → Set where
  node : ∀ {hˡ hʳ} (bal : hˡ ∼ hʳ) → Tree (max bal)

-- 'test' only passes if we split first on 'Tree hˡ' and then on 'hˡ ∼ hʳ'
-- This refutes a split strategy that prefers all-constructor columns
-- over those with catch-alls.
test : ∀ {hˡ hʳ} → Tree hˡ → hˡ ∼ hʳ → Set
test (node pr) pr = ℕ
test (node eq) pr = ℕ
test x         eq = ℕ

{- We cannot split on 'Tree hˡ' if we have already split on 'hˡ ∼ hʳ'
bla : ∀ {hˡ hʳ} → Tree hˡ → hˡ ∼ hʳ → Set
bla nod pr = {!nod!}
bla nod eq = {!!}
-}

