module Highlighting where

Set-one : Set₂
Set-one = Set₁

record R (A : Set) : Set-one where
  constructor con

  field X : Set

  F : Set → Set → Set
  F A B = B

  field P : F A X → Set

  -- highlighting of non-terminating definition
  Q : F A X → Set
  Q = Q

postulate P : _

open import Highlighting.M

data D (A : Set) : Set-one where
  d : let X = D in X A

postulate _+_ _×_ : Set → Set → Set

infixl 4 _×_ _+_
  -- Issue #2140: the operators should be highlighted also in the
  -- fixity declaration.

-- Issue #3120, jump-to-definition for record field tags
-- in record expressions and patterns.

anR : ∀ A → R A
anR A = record { X = A ; P = λ _ → A }

idR : ∀ A → R A → R A
idR A r@record { X = X; P = P } = record r { X = X }

record S (A : Set) : Set where
  field
    X : A

idR' : ∀ A → R A → R A
idR' A r@record { X = X; P = P } = record r { X = X }

open S

bla : ∀{A} → A → S A
bla x .X = x

-- Issue #3825: highlighting of unsolved metas in record{M} expressions

record R₂ (A : Set) : Set where
  field
    impl : {a : A} → A

module M {A : Set} where
  impl : {a : A} → A   -- yellow should not be here
  impl {a} = a

r₂ : ∀{A} → R₂ A
r₂ = record {M}  -- just because there is an unsolved meta here

-- End issue #3825

-- Issue #3855: highlighting of quantity attributes.
-- @0 and @erased should be highlighted as symbols.

idPoly0 : {@0 A : Set} → A → A
idPoly0 x = x

idPolyE : {@erased A : Set} → A → A
idPolyE x = x
