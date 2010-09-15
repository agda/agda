------------------------------------------------------------------------
-- Solver for commutative ring or semiring equalities
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

-- Uses ideas from the Coq ring tactic. See "Proving Equalities in a
-- Commutative Ring Done Right in Coq" by Grégoire and Mahboubi. The
-- code below is not optimised like theirs, though.

open import Algebra
open import Algebra.RingSolver.AlmostCommutativeRing

module Algebra.RingSolver
  {r₁ r₂ r₃}
  (Coeff : RawRing r₁)               -- Coefficient "ring".
  (R : AlmostCommutativeRing r₂ r₃)  -- Main "ring".
  (morphism : Coeff -Raw-AlmostCommutative⟶ R)
  where

import Algebra.RingSolver.Lemmas as L; open L Coeff R morphism
private module C = RawRing Coeff
open AlmostCommutativeRing R hiding (zero)
import Algebra.FunctionProperties as P; open P _≈_
open import Algebra.Morphism
open _-Raw-AlmostCommutative⟶_ morphism renaming (⟦_⟧ to ⟦_⟧')
import Algebra.Operations as Ops; open Ops semiring

open import Relation.Binary
import Relation.Binary.PropositionalEquality as PropEq
import Relation.Binary.Reflection as Reflection

open import Data.Nat using (ℕ; suc; zero) renaming (_+_ to _ℕ-+_)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec
open import Function hiding (type-signature)
open import Level

infix  9 _↑ :-_ -‿NF_
infixr 9 _:^_ _^-NF_ _:↑_
infix  8 _*x _*x+_
infixl 8 _:*_ _*-NF_ _↑-*-NF_
infixl 7 _:+_ _+-NF_ _:-_
infixl 0 _∶_

------------------------------------------------------------------------
-- Polynomials

data Op : Set where
  [+] : Op
  [*] : Op

-- The polynomials are indexed over the number of variables.

data Polynomial (m : ℕ) : Set r₁ where
  op   : (o : Op) (p₁ : Polynomial m) (p₂ : Polynomial m) → Polynomial m
  con  : (c : C.Carrier) → Polynomial m
  var  : (x : Fin m) → Polynomial m
  _:^_ : (p : Polynomial m) (n : ℕ) → Polynomial m
  :-_  : (p : Polynomial m) → Polynomial m

-- Short-hand notation.

_:+_ : ∀ {n} → Polynomial n → Polynomial n → Polynomial n
_:+_ = op [+]

_:*_ : ∀ {n} → Polynomial n → Polynomial n → Polynomial n
_:*_ = op [*]

_:-_ : ∀ {n} → Polynomial n → Polynomial n → Polynomial n
x :- y = x :+ :- y

-- Semantics.

sem : Op → Op₂ Carrier
sem [+] = _+_
sem [*] = _*_

⟦_⟧ : ∀ {n} → Polynomial n → Vec Carrier n → Carrier
⟦ op o p₁ p₂ ⟧ ρ = ⟦ p₁ ⟧ ρ ⟨ sem o ⟩ ⟦ p₂ ⟧ ρ
⟦ con c ⟧      ρ = ⟦ c ⟧'
⟦ var x ⟧      ρ = lookup x ρ
⟦ p :^ n ⟧     ρ = ⟦ p ⟧ ρ ^ n
⟦ :- p ⟧       ρ = - ⟦ p ⟧ ρ

-- Equality.

_≛_ : ∀ {n} → Polynomial n → Polynomial n → Set _
p₁ ≛ p₂ = ∀ {ρ} → ⟦ p₁ ⟧ ρ ≈ ⟦ p₂ ⟧ ρ

private

  -- Reindexing.

  _:↑_ : ∀ {n} → Polynomial n → (m : ℕ) → Polynomial (m ℕ-+ n)
  op o p₁ p₂ :↑ m = op o (p₁ :↑ m) (p₂ :↑ m)
  con c      :↑ m = con c
  var x      :↑ m = var (Fin.raise m x)
  (p :^ n)   :↑ m = (p :↑ m) :^ n
  (:- p)     :↑ m = :- (p :↑ m)

------------------------------------------------------------------------
-- Normal forms of polynomials

-- The normal forms (Horner forms) are indexed over
-- * the number of variables in the polynomial, and
-- * an equivalent polynomial.

data Normal : (n : ℕ) → Polynomial n → Set (r₁ ⊔ r₂ ⊔ r₃) where
  con   : (c : C.Carrier) → Normal 0 (con c)
  _↑    : ∀ {n p'} (p : Normal n p') → Normal (suc n) (p' :↑ 1)
  _*x+_ : ∀ {n p' c'} (p : Normal (suc n) p') (c : Normal n c') →
          Normal (suc n) (p' :* var zero :+ c' :↑ 1)
  _∶_   : ∀ {n p₁ p₂} (p : Normal n p₁) (eq : p₁ ≛ p₂) → Normal n p₂

⟦_⟧-Normal : ∀ {n p} → Normal n p → Vec Carrier n → Carrier
⟦ p ∶ _   ⟧-Normal ρ       = ⟦ p ⟧-Normal ρ
⟦ con c   ⟧-Normal ρ       = ⟦ c ⟧'
⟦ p ↑     ⟧-Normal (x ∷ ρ) = ⟦ p ⟧-Normal ρ
⟦ p *x+ c ⟧-Normal (x ∷ ρ) = (⟦ p ⟧-Normal (x ∷ ρ) * x) + ⟦ c ⟧-Normal ρ

------------------------------------------------------------------------
-- Normalisation

private

  con-NF : ∀ {n} → (c : C.Carrier) → Normal n (con c)
  con-NF {zero}  c = con c
  con-NF {suc _} c = con-NF c ↑

  _+-NF_ : ∀ {n p₁ p₂} → Normal n p₁ → Normal n p₂ → Normal n (p₁ :+ p₂)
  (p₁ ∶ eq₁) +-NF (p₂ ∶ eq₂) = p₁ +-NF p₂                    ∶ eq₁  ⟨ +-cong ⟩ eq₂
  (p₁ ∶ eq)  +-NF p₂         = p₁ +-NF p₂                    ∶ eq   ⟨ +-cong ⟩ refl
  p₁         +-NF (p₂ ∶ eq)  = p₁ +-NF p₂                    ∶ refl ⟨ +-cong ⟩ eq
  con c₁     +-NF con c₂     = con (C._+_ c₁ c₂)             ∶ +-homo _ _
  p₁ ↑       +-NF p₂ ↑       = (p₁ +-NF p₂) ↑                ∶ refl
  p₁ *x+ c₁  +-NF p₂ ↑       = p₁ *x+ (c₁ +-NF p₂)           ∶ sym (+-assoc _ _ _)
  p₁ *x+ c₁  +-NF p₂ *x+ c₂  = (p₁ +-NF p₂) *x+ (c₁ +-NF c₂) ∶ lemma₁ _ _ _ _ _
  p₁ ↑       +-NF p₂ *x+ c₂  = p₂ *x+ (p₁ +-NF c₂)           ∶ lemma₂ _ _ _

  _*x : ∀ {n p} → Normal (suc n) p → Normal (suc n) (p :* var zero)
  p *x = p *x+ con-NF C.0# ∶ lemma₀ _

  mutual

    -- The first function is just a variant of _*-NF_ which I used to
    -- make the termination checker believe that the code is
    -- terminating.

    _↑-*-NF_ : ∀ {n p₁ p₂} →
               Normal n p₁ → Normal (suc n) p₂ →
               Normal (suc n) (p₁ :↑ 1 :* p₂)
    p₁ ↑-*-NF (p₂ ∶ eq)   = p₁ ↑-*-NF p₂                    ∶ refl ⟨ *-cong ⟩ eq
    p₁ ↑-*-NF p₂ ↑        = (p₁ *-NF p₂) ↑                  ∶ refl
    p₁ ↑-*-NF (p₂ *x+ c₂) = (p₁ ↑-*-NF p₂) *x+ (p₁ *-NF c₂) ∶ lemma₄ _ _ _ _

    _*-NF_ : ∀ {n p₁ p₂} →
             Normal n p₁ → Normal n p₂ → Normal n (p₁ :* p₂)
    (p₁ ∶ eq₁)  *-NF (p₂ ∶ eq₂)  = p₁ *-NF p₂                      ∶ eq₁  ⟨ *-cong ⟩ eq₂
    (p₁ ∶ eq)   *-NF p₂          = p₁ *-NF p₂                      ∶ eq   ⟨ *-cong ⟩ refl
    p₁          *-NF (p₂ ∶ eq)   = p₁ *-NF p₂                      ∶ refl ⟨ *-cong ⟩ eq
    con c₁      *-NF con c₂      = con (C._*_ c₁ c₂)               ∶ *-homo _ _
    p₁ ↑        *-NF p₂ ↑        = (p₁ *-NF p₂) ↑                  ∶ refl
    (p₁ *x+ c₁) *-NF p₂ ↑        = (p₁ *-NF p₂ ↑) *x+ (c₁ *-NF p₂) ∶ lemma₃ _ _ _ _
    p₁ ↑        *-NF (p₂ *x+ c₂) = (p₁ ↑ *-NF p₂) *x+ (p₁ *-NF c₂) ∶ lemma₄ _ _ _ _
    (p₁ *x+ c₁) *-NF (p₂ *x+ c₂) =
      (p₁ *-NF p₂) *x *x +-NF
      (p₁ *-NF c₂ ↑ +-NF c₁ ↑-*-NF p₂) *x+ (c₁ *-NF c₂)            ∶ lemma₅ _ _ _ _ _

  -‿NF_ : ∀ {n p} → Normal n p → Normal n (:- p)
  -‿NF (p ∶ eq)  = -‿NF p ∶ -‿cong eq
  -‿NF con c     = con (C.-_ c) ∶ -‿homo _
  -‿NF (p ↑)     = (-‿NF p) ↑
  -‿NF (p *x+ c) = -‿NF p *x+ -‿NF c ∶ lemma₆ _ _ _

  var-NF : ∀ {n} → (i : Fin n) → Normal n (var i)
  var-NF zero    = con-NF C.1# *x+ con-NF C.0# ∶ lemma₇ _
  var-NF (suc i) = var-NF i ↑

  _^-NF_ : ∀ {n p} → Normal n p → (i : ℕ) → Normal n (p :^ i)
  p ^-NF zero  = con-NF C.1#     ∶ 1-homo
  p ^-NF suc n = p *-NF p ^-NF n ∶ refl

  normaliseOp : ∀ (o : Op) {n p₁ p₂} →
                Normal n p₁ → Normal n p₂ → Normal n (p₁ ⟨ op o ⟩ p₂)
  normaliseOp [+] = _+-NF_
  normaliseOp [*] = _*-NF_

normalise : ∀ {n} (p : Polynomial n) → Normal n p
normalise (op o p₁ p₂) = normalise p₁ ⟨ normaliseOp o ⟩ normalise p₂
normalise (con c)      = con-NF c
normalise (var i)      = var-NF i
normalise (p :^ n)     = normalise p ^-NF n
normalise (:- p)       = -‿NF normalise p

⟦_⟧↓ : ∀ {n} → Polynomial n → Vec Carrier n → Carrier
⟦ p ⟧↓ ρ = ⟦ normalise p ⟧-Normal ρ

------------------------------------------------------------------------
-- Correctness

private
  sem-cong : ∀ op → sem op Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  sem-cong [+] = +-cong
  sem-cong [*] = *-cong

  raise-sem : ∀ {n x} (p : Polynomial n) ρ →
              ⟦ p :↑ 1 ⟧ (x ∷ ρ) ≈ ⟦ p ⟧ ρ
  raise-sem (op o p₁ p₂) ρ = raise-sem p₁ ρ ⟨ sem-cong o ⟩
                             raise-sem p₂ ρ
  raise-sem (con c)      ρ = refl
  raise-sem (var x)      ρ = refl
  raise-sem (p :^ n)     ρ = raise-sem p ρ ⟨ ^-cong ⟩
                             PropEq.refl {x = n}
  raise-sem (:- p)       ρ = -‿cong (raise-sem p ρ)

  nf-sound : ∀ {n p} (nf : Normal n p) ρ →
             ⟦ nf ⟧-Normal ρ ≈ ⟦ p ⟧ ρ
  nf-sound (nf ∶ eq)         ρ       = nf-sound nf ρ ⟨ trans ⟩ eq
  nf-sound (con c)           ρ       = refl
  nf-sound (_↑ {p' = p'} nf) (x ∷ ρ) =
    nf-sound nf ρ ⟨ trans ⟩ sym (raise-sem p' ρ)
  nf-sound (_*x+_ {c' = c'} nf₁ nf₂) (x ∷ ρ) =
    (nf-sound nf₁ (x ∷ ρ) ⟨ *-cong ⟩ refl)
      ⟨ +-cong ⟩
    (nf-sound nf₂ ρ ⟨ trans ⟩ sym (raise-sem c' ρ))

-- Completeness can presumably also be proved (i.e. the normal forms
-- should be unique, if the casts are ignored).

------------------------------------------------------------------------
-- "Tactics"

open Reflection setoid var ⟦_⟧ ⟦_⟧↓ (nf-sound ∘ normalise)
  public using (prove; solve) renaming (_⊜_ to _:=_)

-- For examples of how solve and _:=_ can be used to
-- semi-automatically prove ring equalities, see, for instance,
-- Data.Digit or Data.Nat.DivMod.
