{-# OPTIONS --universe-polymorphism #-}
-- {-# OPTIONS --verbose tc.records.ifs:15 #-}
-- {-# OPTIONS --verbose tc.constr.findInScope:15 #-}
-- {-# OPTIONS --verbose tc.term.args.ifs:15 #-}
-- {-# OPTIONS --verbose cta.record.ifs:15 #-}
-- {-# OPTIONS --verbose tc.section.apply:25 #-}
-- {-# OPTIONS --verbose tc.mod.apply:100 #-}
-- {-# OPTIONS --verbose scope.rec:15 #-}
-- {-# OPTIONS --verbose tc.rec.def:15 #-}

module 07-subclasses where

module Imports where
  module L where
    postulate
      Level : Set
      zero  : Level
      suc   : Level → Level
      _⊔_   : Level → Level → Level

    {-# BUILTIN LEVEL     Level #-}
    {-# BUILTIN LEVELZERO zero  #-}
    {-# BUILTIN LEVELSUC  suc   #-}
    {-# BUILTIN LEVELMAX  _⊔_   #-}

  -- extract from Function
  id : ∀ {a} {A : Set a} → A → A
  id x = x

  _$_ : ∀ {a b} {A : Set a} {B : A → Set b} →
        ((x : A) → B x) → ((x : A) → B x)
  f $ x = f x

  _∘_ : ∀ {a b c}
          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
  f ∘ g = λ x → f (g x)

  -- extract from Data.Bool
  infixr 5 _∨_ 
  data Bool : Set where
    true  : Bool
    false : Bool

  not : Bool → Bool
  not true  = false
  not false = true

  _∨_ : Bool → Bool → Bool
  true  ∨ b = true
  false ∨ b = b

  -- extract from Relation.Nullary.Decidable and friends
  infix 3 ¬_

  data ⊥ : Set where

  ¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
  ¬ P = P → ⊥

  data Dec {p} (P : Set p) : Set p where
    yes : ( p :   P) → Dec P
    no  : (¬p : ¬ P) → Dec P
  ⌊_⌋ : ∀ {p} {P : Set p} → Dec P → Bool
  ⌊ yes _ ⌋ = true
  ⌊ no  _ ⌋ = false


  -- extract from Relation.Binary.PropositionalEquality
  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    refl : x ≡ x

  cong : ∀ {a b} {A : Set a} {B : Set b}
         (f : A → B) {x y} → x ≡ y → f x ≡ f y
  cong f refl = refl

  -- extract from Data.Nat
  data ℕ : Set where
    zero : ℕ
    suc  : (n : ℕ) → ℕ

  {-# BUILTIN NATURAL ℕ    #-}
  {-# BUILTIN ZERO    zero #-}
  {-# BUILTIN SUC     suc  #-}

  pred : ℕ → ℕ
  pred zero    = zero
  pred (suc n) = n

  _≟_ : (x y : ℕ) → Dec (x ≡ y)
  zero  ≟ zero   = yes refl
  suc m ≟ suc n  with m ≟ n
  suc m ≟ suc .m | yes refl = yes refl
  suc m ≟ suc n  | no prf   = no (prf ∘ cong pred)
  zero  ≟ suc n  = no λ()
  suc m ≟ zero   = no λ()

open Imports

-- Begin of actual example!

record Eq (A : Set) : Set where
  field eq : A → A → Bool

primEqBool : Bool → Bool → Bool
primEqBool true = id
primEqBool false = not

eqBool : Eq Bool
eqBool = record { eq = primEqBool }

primEqNat : ℕ → ℕ → Bool
primEqNat a b = ⌊ a ≟ b ⌋

primLtNat : ℕ → ℕ → Bool
primLtNat 0 _ = true
primLtNat (suc a) (suc b) = primLtNat a b
primLtNat _ _ = false

neq : {t : Set} → {{eqT : Eq t}} → t → t → Bool
neq a b = not $ eq a b
  where open Eq {{...}}

record Ord₁ (A : Set) : Set where
  field _<_ : A → A → Bool
        eqA : Eq A

ord₁Nat : Ord₁ ℕ
ord₁Nat = record { _<_ = primLtNat; eqA = eqNat }
  where eqNat : Eq ℕ
        eqNat = record { eq = primEqNat }


record Ord₂ {A : Set} (eqA : Eq A) : Set where
  field _<_ : A → A → Bool

ord₂Nat : Ord₂ (record { eq = primEqNat })
ord₂Nat = record { _<_ = primLtNat }


record Ord₃ (A : Set) : Set where
  field _<_ : A → A → Bool
        eqA : Eq A
  open Eq eqA public

ord₃Nat : Ord₃ ℕ
ord₃Nat = record { _<_ = primLtNat; eqA = eqNat }
  where eqNat : Eq ℕ
        eqNat = record { eq = primEqNat }

record Ord₄ {A : Set} (eqA : Eq A) : Set where
  field _<_ : A → A → Bool
  open Eq eqA public

ord₄Nat : Ord₄ (record { eq = primEqNat })
ord₄Nat = record { _<_ = primLtNat }


module test₁ where
  open Ord₁ {{...}}
  open Eq {{...}}

  eqNat : Eq _
  eqNat = eqA

  test₁ = 5 < 3
  test₂ = eq 5 3
  test₃ = eq true false
  test₄ : {A : Set} → {{ ordA : Ord₁ A }} → A → A → Bool
  test₄ a b = a < b ∨ eq a b 
    where
      eqA' : Eq _
      eqA' = eqA

module test₂ where
  open Ord₂ {{...}}
  open Eq {{...}}

  eqNat : Eq ℕ
  eqNat = record { eq = primEqNat }

  test₁ = 5 < 3
  test₂ = eq 5 3
  test₃ = eq true false
  test₄ : {A : Set} → {eqA : Eq A} → {{ ordA : Ord₂ eqA }} → A → A → Bool
  test₄ {eqA = _} a b = a < b ∨ eq a b 


module test₃ where
  open Ord₃ {{...}}
  open Eq {{...}} renaming (eq to eq')

  test₁ = 5 < 3
  test₂ = eq 5 3
  test₃ = eq' true false
  test₄ : {A : Set} → {{ ordA : Ord₃ A }} → A → A → Bool
  test₄ a b = a < b ∨ eq a b 

module test₄ where
  open Ord₄ {{...}}
  open Eq {{...}} renaming (eq to eq')

  test₁ = 5 < 3
  test₂ = eq 5 3
  test₃ = eq' true false
  test₄ : {A : Set} → {eqA : Eq A} → {{ ordA : Ord₄ eqA }} → A → A → Bool
  test₄ a b = a < b ∨ eq a b 

module test₄′ where
  open Ord₄ {{...}} hiding (eq)
  open Eq {{...}}

  eqNat : Eq ℕ
  eqNat = record { eq = primEqNat }

  test₁ = 5 < 3
  test₂ = eq 5 3
  test₃ = eq true false
  test₄ : {A : Set} → {eqA : Eq A} → {{ ordA : Ord₄ eqA }} → A → A → Bool
  test₄ {eqA = _} a b = a < b ∨ eq a b 

