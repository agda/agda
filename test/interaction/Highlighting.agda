{-# OPTIONS --cohesion --erasure --guarded #-}

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

open import Highlighting.M using (ℕ) renaming
  ( _+_ to infixl 5 _⊕_
  ; _*_ to infixl 7 _⊗_
  )

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

-- Issue #3989: Shadowed repeated variables in telescopes should by
-- default /not/ be highlighted.

Issue-3989 : (A A : Set) → Set
Issue-3989 _ A = A

-- Issue #4356.

open import Agda.Builtin.Sigma

Issue-4356₁ : Σ Set (λ _ → Set) → Σ Set (λ _ → Set)
Issue-4356₁ = λ P@(A , B) → P

Issue-4356₂ : Σ Set (λ _ → Set) → Set
Issue-4356₂ = λ (A , B) → A

Issue-4356₃ : Σ Set (λ _ → Set) → Σ Set (λ _ → Set)
Issue-4356₃ P = let Q@(A , B) = P in Q

Issue-4356₄ : Σ Set (λ _ → Set) → Set
Issue-4356₄ P = let (A , B) = P in B

Issue-4356₅ : Σ Set (λ _ → Set) → Σ Set (λ _ → Set)
Issue-4356₅ P@(A , B) = P

Issue-4356₆ : Σ Set (λ _ → Set) → Set
Issue-4356₆ (A , B) = B

-- Issue #4361: Highlighting builtins.

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}  -- NATURAL should be highlighted as keyword.

module Issue3432 where

  pattern con′ x y = con x y
  pattern d′       = d

open Issue3432 using (con′; d′)
  -- These pattern synonyms should be highlighted
  -- in inductive constructor color.

module Issue4604 where

  record RR : Set₁ where
    field
      A : Set

  postulate
    rr : RR

  open RR rr

  rr₁ : RR
  rr₁ = record { A = A }  -- Second A should /not/ be highlighted as projection.

  rr₂ : RR
  rr₂ = record { A = RR.A rr }  -- All other As should have field/projection color.

-- Highlighting of dot patterns.

module Issue5233 where

  data IsSet : Set₁ → Set where
    isSet : IsSet Set

  highlight-dot-Set : (A : Set₁) → IsSet A → Set
  highlight-dot-Set .Set isSet = Nat
                 -- ^^^^ should be highlighted

  data Vec (A : Set) : Nat → Set where
    nil  : Vec A zero
    cons : (n : Nat) (x : A) (xs : Vec A n) → Vec A (suc n)

  idVec : ∀ {A n} → Vec A n → Vec A n
  idVec {n = .(zero)}  nil           = nil
  idVec {n = .(suc k)} (cons k x xs) = cons _ x (idVec xs)
           -- ^^^^^^^ should be highlighted

-- Highlighting of erased pattern-matching lambdas and warnings coming
-- from the Happy parser.

module Issue4525 where

  @0 _ : Set → Set
  _ = λ @0 { A → A }

  @0 _ : Set → Set
  _ =
    λ @0
      @ω
      @erased
      @plenty
      @(tactic (λ _ → Set))
      @irr
      @irrelevant
      @shirr
      @shape-irrelevant
      @relevant
      @♭
      @flat
      @notlock
      @lock
      @tick where
      A → A

-- Highlighting of erased data and record types and modules.

module Issue4743 where

  data @0 D₁ : Set where

  data @0 D₂ : Set

  data D₂ where

  interleaved mutual

    data @0 D₃ : Set where

    data D₃ where
      @ω c : D₃

  record @0 R₁ : Set where
    @ω A : Set₁
    A = Set

  record @0 R₃ : Set

  record R₃ where

  module @0 _ where

  module @0 M₁ where

  F : let module @0 M₂ = M₁ in Set₁
  F = Set
    module @0 @plenty @lock _ where
      @plenty A : Set₁
      A = Set

  module @0 M₂ = M₁
