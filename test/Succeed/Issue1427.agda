-- Andreas, 2015-01-19  Forced constructor arguments should not
-- give rise to unification constraints.

-- Andreas, 2015-02-27  Forcing analysis is too fragile to have
-- such a huge impact.  The problem has to be addressed by
-- putting heterogeneous unification on a solid foundation.

-- {-# OPTIONS -v tc.lhs.unify:15 #-}
-- {-# OPTIONS -v tc.force:10 #-}

open import Common.Equality
open import Common.Prelude

data HEq (A : Set) (a : A) : (B : Set) (b : B) → Set1 where
  refl : HEq A a A a

module Forcing where

  data Fin : (n : Nat) → Set where
    zero : {n : Nat}             → Fin (suc n)
    suc  : {n : Nat} (i : Fin n) → Fin (suc n)


  inj-Fin-≅ : ∀ {n m} {i : Fin n} {j : Fin m} → HEq (Fin n) i (Fin m) j → n ≡ m
  inj-Fin-≅ {i = zero}  {zero  } refl = refl  -- Expected to fail, as n /= m
  inj-Fin-≅ {i = zero}  {suc  j} ()
  inj-Fin-≅ {i = suc i} {zero  } ()
  inj-Fin-≅ {i = suc i} {suc .i} refl = refl  -- Expected to fail, as n /= m

  -- This should not be accepted, as the direct attempt also fails:

  -- inj-Fin-≅' : ∀ {n m} {i : Fin n} {j : Fin m} → HEq (Fin n) i (Fin m) j → n ≡ m
  -- inj-Fin-≅' refl = refl

module NoForcing where

  -- Abstracting over suc disables forcing [Issue 1427]
  module M (s : Nat → Nat) where

    data Fin : (n : Nat) → Set where
      zero : {n : Nat}             → Fin (s n)
      suc  : {n : Nat} (i : Fin n) → Fin (s n)

  open M suc

  inj-Fin-≅ : ∀ {n m} {i : Fin n} {j : Fin m} → HEq (Fin n) i (Fin m) j → n ≡ m
  inj-Fin-≅ {i = zero}  {zero  } refl = refl  -- Expected to fail, as n /= m
  inj-Fin-≅ {i = zero}  {suc  j} ()
  inj-Fin-≅ {i = suc i} {zero  } ()
  inj-Fin-≅ {i = suc i} {suc .i} refl = refl  -- Expected to fail, as n /= m

  -- This should not be accepted, as the direct attempt also fails:

  -- inj-Fin-≅' : ∀ {n m} {i : Fin n} {j : Fin m} → HEq (Fin n) i (Fin m) j → n ≡ m
  -- inj-Fin-≅' refl = refl

-- Update [Issue 1427]:  For now, this is accepted again,
-- as forcing analysis can be easily circumvented (module NoForcing).
