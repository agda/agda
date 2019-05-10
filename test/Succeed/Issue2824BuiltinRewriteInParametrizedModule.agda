-- Andreas, 2017-11-01, issue #2824
-- allow built-in pragmas in parametrized modules

{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality

module _ (A : Set) where  -- This is the top-level module header.

{-# BUILTIN REWRITE _≡_ #-}

postulate
  P : A → Set
  a b : A
  a→b : a ≡ b

{-# REWRITE a→b #-}

test : P a → P b
test x = x

-- Should succeed.
