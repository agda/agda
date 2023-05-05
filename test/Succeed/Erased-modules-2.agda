{-# OPTIONS --erasure #-}

module Erased-modules-2 where

-- Everything in this local module is erased.

module @0 M (@0 A : Set) where

  B : Set
  B = A

  -- Also definitions inside the following module which is not marked
  -- as erased.

  module M′ where

    C : Set
    C = A

  -- Also the following pattern-matching lambda.

  F : @0 Set → Set
  F = λ { A → A }

  -- Also the following definitions/modules which are marked as not
  -- being erased.

  @plenty D : Set
  D = A

  G : @0 Set → Set
  G = λ @ω { A → A }

  module @ω M″ where

    -- However, it is fine to use @ω in types.

    C : @ω Set → Set
    C _ = A

  data @ω E : Set where
    @plenty c : E

  record @ω R : Set₁ where
    constructor q
    field
      @ω C : Set

    @plenty C′ : Set
    C′ = C″
      module @ω _ where
        C″ = C

-- If an erased module is opened "publicly", then the re-exported
-- definitions are erased.

import Agda.Builtin.Bool
open module @0 B = Agda.Builtin.Bool public

@0 _ : Bool
_ = true

-- Erased modules can be used to instantiate erased record fields.

record R : Set₂ where
  field
    A    : Set₁
    @0 B : @0 A → A

r : R
r = record { A = Set; M }

-- Everything in the following anonymous module is also erased.

module @0 _ where

  F : @0 Set → Set
  F A = A

G : Set₁
G = Set
  -- Everything in the where module is erased.
  module @0 _ where

    H : @0 Set → Set
    H A = A

    -- Even if it is marked as not being erased.

    @ω I : @0 Set → Set
    I A = A

record Erased (@0 A : Set) : Set where
  field
    @0 erased : A

-- Everything in the module M′ is erased.

J : @0 Set → Set
J A = let module @0 M′ = M A in Erased M′.B

-- Everything in the module M₁ is erased.

module @0 M₁ (A : Set) = M A

-- Everything in the module M₂ is erased. It is fine to use an erased
-- argument when instantiating M₁, even though the only argument of M₁
-- is not erased.

open module @0 M₂ (@0 A : Set) = M₁ A
