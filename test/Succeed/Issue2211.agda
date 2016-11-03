-- Andreas, 2016-11-03, issue #2211
-- The occurs check did not take variables labeled as `UnusedArg`
-- on the left hand side into consideration.

-- {-# OPTIONS -v tc.check.term:40 #-}
-- {-# OPTIONS -v tc.meta:45 #-}
-- {-# OPTIONS -v tc.polarity:20 #-}

open import Agda.Builtin.Equality
open import Common.Nat

cong : ∀{A B : Set}(f : A → B) (x y : A) → x ≡ y → f x ≡ f y
cong _ _ _ refl = refl

data ⊥ : Set where

⊥-elim : ∀{A : Set} → ⊥ {- unused arg -} → A
⊥-elim ()

data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc  : {n : Nat} (i : Fin n) → Fin (suc n)

toNat : ∀ {n} → Fin n → Nat
toNat zero    = 0
toNat (suc i) = suc (toNat i)

tighten : ∀ n (x : Fin (suc n)) (neq : (toNat x ≡ n → ⊥) {- unused arg x-}) → Fin n
tighten zero    zero    neq = ⊥-elim (neq refl)
tighten (suc n) zero    neq = zero
tighten zero    (suc ())
tighten (suc n) (suc x) neq = suc (tighten n x (λ p → neq (cong suc _ _ p)))

tighten-correct : ∀ n (x : Fin (suc n)) (neq : toNat x ≡ n → ⊥) →
  toNat (tighten n x neq) ≡ toNat x
tighten-correct zero    zero    neq = ⊥-elim (neq refl)
tighten-correct (suc n) zero    neq = refl
tighten-correct zero    (suc ())
tighten-correct (suc n) (suc x) neq =
  cong suc _ _ (tighten-correct n x (λ p → neq (cong Nat.suc  _ _ p)))

-- ERROR WAS:
-- Cannot instantiate ... because it contains the variable neg ...

-- Should succeed.

{-
term _62 n x neq
     (toNat (tighten n x (λ p → neq (cong suc p)))) := suc
                                                       (toNat
                                                        (tighten n x (λ p → neq (cong suc p))))
term _62 n x neq (toNat x) := toNat (suc x)

after kill analysis
  metavar = _62
  kills   = [False,False,True,False]
  kills'  = [ru(False),ru(False),ru(True),ru(False)]
  oldType = (n₁ : Nat) (x₁ : Fin (suc n₁))
            (neq₁ : toNat (suc x₁) ≡ suc n₁ → ⊥) →
            Nat → Nat
  newType = (n₁ : Nat) → Fin (suc n₁) → Nat → Nat
actual killing
  new meta: _69
  kills   : [ru(False),ru(False),ru(True),ru(False)]
  inst    : _62 := _69 @3 n neq

term _69 n x (toNat (tighten n x (λ p → neq (cong suc p)))) := suc
                                                               (toNat
                                                                (tighten n x
                                                                 (λ p → neq (cong suc p))))

Here, the variable neq on the lhs was not considered eligible for occurrence on the rhs
since it is contained in an unused arg only.
-}
