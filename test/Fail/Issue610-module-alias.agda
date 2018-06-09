-- Andreas, 2016-02-11, bug reported by sanzhiyan

{-# OPTIONS --irrelevant-projections #-}

module Issue610-module-alias where

import Common.Level
open import Common.Equality

data ⊥ : Set where
record ⊤ : Set where

data A : Set₁ where
  set : .Set → A

module M .(x : Set) where

  .out : _
  out = x

.ack : A → Set
ack (set x) = M.out x

hah : set ⊤ ≡ set ⊥
hah = refl

.moo' : ⊥
moo' = subst (λ x → x) (cong ack hah) _

-- Expected error:
-- .(⊥) !=< ⊥ of type Set
-- when checking that the expression subst (λ x → x) (cong ack hah) _ has type ⊥

baa : .⊥ → ⊥
baa ()

yoink : ⊥
yoink = baa moo'
