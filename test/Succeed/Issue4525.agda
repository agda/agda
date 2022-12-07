{-# OPTIONS --cohesion --erasure #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Unit

postulate
  @0 A : Set

@0 _ : @0 Set → (Set → Set) → Set
_ = λ @0 where
  A G → G A

@0 _ : @0 Set → (Set → Set) → Set
_ = λ @0 { A G → G A }

data ⊥ : Set where

@0 _ : @0 ⊥ → Set
_ = λ @0 { () }

@0 _ : @0 ⊥ → Set
_ = λ @0 where
  ()

@0 _ : @0 ⊥ → Set
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
    ()

F : ⊤ → ⊤
F = λ { tt → tt }

macro

  `F : Term → TC ⊤
  `F goal = do
    F ← withNormalisation true (quoteTC F)
    F ← quoteTC F
    unify goal F

_ :
  `F ≡
  pat-lam
    (clause []
      (arg (arg-info visible (modality relevant quantity-ω))
         (con (quote tt) []) ∷
       [])
      (con (quote tt) []) ∷
     [])
    []
_ = refl
