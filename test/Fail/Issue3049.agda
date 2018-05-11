-- Andreas, 2018-05-11, issue #3049 reported by Ulf
-- Positivity checker too optimistic about polarity of arguments
-- beyond the formal function arity.

-- Backwards-compatible version of the test case.

-- {-# OPTIONS -v tc.pos.args:100 #-}

module Issue3049 where

data Bool : Set where
  true false : Bool

T : Bool → Set₁
T true  = Set → Set
T false = Set

bad : ∀ b → T b
bad true   = λ A → A → A   -- negative A
bad false  = Bool

F : Bool → ∀ b → T b
F true  b       = bad b  -- is not (can't be) eta-expanded
F false true    = λ A → A
F false false   = Bool

-- Should fail positivity check:

data D : Set where
  nop : (b : Bool) → F b true D → D

data ⊥ : Set where

d : D
d = nop true (λ x → x)

!d : D → ⊥
!d (nop true  f) = !d (f d)
!d (nop false x) = !d x

loop : ⊥
loop = !d d
