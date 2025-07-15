-- Andreas, 2025-07-03, issue #7987
-- Attributes are now supported on function clauses.

{-# OPTIONS --erasure #-}

@0 id0 : (A : Set) → A → A
@0 id0 A x = x

@ω idω : (A : Set) → A → A
@ω idω A x = x

-- Should succeed.

S : Set₁
@(tactic _) S = Set  -- warning: -W[no]MisplacedAttributes

-- Modality in clause needs to fit modality of type signature

id1 : (A : Set) → A → A
@0 id1 A x = x    -- warning about ignored @0

@ω id2 : (A : Set) → A → A
@0 id2 A x = x    -- warning about ignored @0

@0 id3 : (A : Set) → A → A
@ω id3 A x = x    -- warning about ignored @ω

open import Agda.Builtin.Nat

idN : Nat → Nat
idN zero = zero
@0 idN (suc n) = suc (idN zero)   -- warning about ignored @0

@0 idN0 : Nat → Nat
idN0 zero = zero
@ω idN0 (suc n) = suc (idN zero)  -- warning about ignored @ω
