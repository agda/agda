-- Andreas, 2017-11-01, issue #2824
-- allow built-in pragmas before top-level module header

{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality

{-# BUILTIN REWRITE _≡_ #-}

module Issue2824 (A : Set) where  -- This is the top-level module header.

postulate
  P : A → Set
  a b : A
  a→b : a ≡ b

{-# REWRITE a→b #-}

test : P a → P b
test x = x

-- Should succeed.
