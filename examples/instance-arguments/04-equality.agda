{-# OPTIONS --universe-polymorphism #-}
-- {-# OPTIONS --verbose tc.records.ifs:15 #-}
-- {-# OPTIONS --verbose tc.constr.findInScope:15 #-}
-- {-# OPTIONS --verbose tc.term.args.ifs:15 #-}
-- {-# OPTIONS --verbose cta.record.ifs:15 #-}
-- {-# OPTIONS --verbose tc.section.apply:25 #-}
-- {-# OPTIONS --verbose tc.mod.apply:100 #-}
-- {-# OPTIONS --verbose scope.rec:15 #-}
-- {-# OPTIONS --verbose tc.rec.def:15 #-}

module 04-equality where

record ⊤ : Set where
  constructor tt

data Bool : Set where
  true : Bool
  false : Bool

or : Bool → Bool → Bool
or true _ = true
or _ true = true
or false false = false

and : Bool → Bool → Bool
and false _ = false
and _ false = false
and true true = false

not : Bool → Bool
not true = false
not false = true

id : {A : Set} → A → A
id v = v

primEqBool : Bool → Bool → Bool
primEqBool true = id
primEqBool false = not

record Eq (A : Set) : Set where
  field eq : A → A → Bool


eqBool : Eq Bool
eqBool = record { eq = primEqBool }

open Eq {{...}}

neq : {t : Set} → {{eqT : Eq t}} → t → t → Bool
neq a b = not (eq a b)

test = eq false false


-- Instance arguments will also resolve to candidate instances which
-- still require hidden arguments. This allows us to define a
-- reasonable instance for Fin types
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)



primEqFin : {n : ℕ} → Fin n → Fin n → Bool
primEqFin zero zero = true
primEqFin zero (suc y) = false
primEqFin (suc y) zero = false
primEqFin (suc x) (suc y) = primEqFin x y

eqFin : {n : ℕ} → Eq (Fin n)
eqFin = record { eq = primEqFin }

-- eqFin′ : Eq (Fin 3)
-- eqFin′ = record { eq = primEqFin }

-- eqFinSpecial : {n : ℕ} → Prime n → Eq (Fin n)
-- eqFinSpecial 

fin1 : Fin 3
fin1 = zero

fin2 : Fin 3
fin2 = suc (suc zero)

testFin : Bool
testFin = eq fin1 fin2
