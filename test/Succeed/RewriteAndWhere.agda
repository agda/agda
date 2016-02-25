-- {-# OPTIONS -v tc.with:40 #-}

module RewriteAndWhere where

open import Common.Equality

data ℕ : Set where
  zero : ℕ

-- good : (a b : ℕ) → a ≡ b → b ≡ a
-- good a b eq with a | eq
-- ... | .b | refl = foo
--   where
--     foo : b ≡ b
--     foo = refl

mutual
  aux : (a b : ℕ)(w : ℕ) → w ≡ b → b ≡ w
  aux a b .b refl = foo
    where
     foo : b ≡ b
     foo = refl

  good₂ : (a b : ℕ) → a ≡ b → b ≡ a
  good₂ a b eq = aux a b a eq

bad : (a b : ℕ) → a ≡ b → b ≡ a
bad a b eq rewrite eq = foo
  where
    foo : b ≡ b
    foo = refl
    -- Andreas, 2014-11-06: this rewrite is trying to touch
    -- variable b bound in pattern of parent function, which is
    -- illegal.
    --
    -- foo rewrite sym eq = bar
    --   where
    --     bar : a ≡ a
    --     bar = refl

-- Andreas, 2015-11-18 added test during exploration of issue 1692.
-- Ulf, 2016-02-25 after fix to #745 this no longer works.
-- test : (a b : ℕ) → a ≡ b → b ≡ a
-- test a b eq with a | eq
-- test a b eq | .b | refl = eq
