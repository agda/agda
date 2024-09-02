{-# OPTIONS --rewriting #-}

-- {-# OPTIONS -v rewriting.rule.check:30 #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

{-# BUILTIN REWRITE _≡_ #-}

funny : true ≡ false → true ≡ false
funny x = x

{-# REWRITE funny #-}  -- RewriteVariablesNotBoundByLHS

-- Andreas, 2024-08-20
-- More cases of illegal rewrite rules.

{-# REWRITE refl #-}   -- RewriteLHSNotDefinitionOrConstructor

record R : Set1 where
  field f : Set

postulate
  proj : ∀ A → R.f ≡ A

{-# REWRITE proj #-}   -- RewriteLHSNotDefinitionOrConstructor
                       -- because Agda sees it as (λ x → x .R.f)
postulate
  A : Set
  a : A
  f g : A → A
  f=g : (λ x → f a) ≡ g

{-# REWRITE f=g #-}   -- RewriteLHSNotDefinitionOrConstructor (lambda)
