-- Andreas, 2016-02-11, bug reported by sanzhiyan

{-# OPTIONS --irrelevant-projections #-}

module Issue610-module where

import Common.Level
open import Common.Equality

data ⊥ : Set where
record ⊤ : Set where

data A : Set₁ where
  set : .Set → A

module M .(x : Set) where

  .out : Set
  out = x

.ack : A → Set
ack (set x) = M.out x

hah : set ⊤ ≡ set ⊥
hah = refl

-- SHOULD FAIL
.moo' : ⊥
moo' = subst (λ x → x) (cong ack hah) _

-- SHOULD FAIL
.moo : ⊥
moo with cong ack hah
moo | q = subst (λ x → x) q _

baa : .⊥ → ⊥
baa ()

yoink : ⊥
yoink = baa moo
