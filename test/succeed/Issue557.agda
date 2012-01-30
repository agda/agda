-- Andreas, 2012-01-30, bug reported by Nisse
-- {-# OPTIONS -v tc.term.absurd:50 -v tc.signature:30 -v tc.conv.atom:30 -v tc.conv.elim:50 #-}
module Issue557 where

data ⊥ : Set where

postulate
  A : Set
  a : (⊥ → ⊥) → A
  F : A → Set
  f : (a : A) → F a

module M (I : Set → Set) where

  x : A
  x = a (λ ())

y : A
y = M.x (λ A → A)

z : F y
z = f y

-- cause was absurd lambda in a module, i.e., under a telescope (I : Set -> Set)
-- (λ ()) must be replaced by (absurd I) not just by (absurd)
