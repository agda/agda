------------------------------------------------------------------------
-- The Agda standard library
--
-- Solver for commutative ring or semiring equalities
------------------------------------------------------------------------

-- Uses ideas from the Coq ring tactic. See "Proving Equalities in a
-- Commutative Ring Done Right in Coq" by Grégoire and Mahboubi. The
-- code below is not optimised like theirs, though (in particular our
-- Horner normal forms are not sparse).

open import Algebra
open import Algebra.RingSolver.AlmostCommutativeRing

open import Relation.Binary

module Algebra.RingSolver
  {r₁ r₂ r₃}
  (Coeff : RawRing r₁)               -- Coefficient "ring".
  (R : AlmostCommutativeRing r₂ r₃)  -- Main "ring".
  (morphism : Coeff -Raw-AlmostCommutative⟶ R)
  (_coeff≟_ : Decidable (coeff≈ morphism))
  where

import Algebra.RingSolver.Lemmas as L; open L Coeff R morphism
private module C = RawRing Coeff
open AlmostCommutativeRing R renaming (zero to zero*)
import Algebra.FunctionProperties as P; open P _≈_
open import Algebra.Morphism
open _-Raw-AlmostCommutative⟶_ morphism renaming (⟦_⟧ to ⟦_⟧')
import Algebra.Operations as Ops; open Ops semiring

open import Relation.Binary
open import Relation.Nullary.Core
import Relation.Binary.PropositionalEquality as PropEq
import Relation.Binary.Reflection as Reflection

open import Data.Empty
open import Data.Product
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec
open import Function
open import Level using (_⊔_)

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

-- The polynomials are indexed on the number of variables.

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

------------------------------------------------------------------------
-- Normal forms of polynomials

-- A univariate polynomial of degree d
--     p = a_d x^d + a_{d-1}x^{d-1} + ... + a_0
-- is represented in Horner normal form by
--     p = ((a_d x + a_{d-1})x + ...)x + a_0
-- Note that a Horner normal form is basically a right-associative list of coefficients, and
-- we can allow the case of an empty list standing for the zero polynomial of degree "-1"

-- Given this representation of univariate polynomials over an arbitrary ring, polynomials
-- in any number of variables over the ring C may be represented by the canonical isomorphisms
--     C[] = C
--     C[X1,...Xn] = C[X1,...,Xn-1][Xn]

mutual
  data HNF : ℕ → Set r₁ where
    ∅ : ∀ {n} → HNF (suc n)
    _*x+_ : ∀ {n} → HNF (suc n) → Normal n → HNF (suc n)
  data Normal : ℕ → Set r₁ where
    con : C.Carrier → Normal zero
    poly : ∀ {n} → HNF (suc n) → Normal (suc n)
  -- Note that these datatypes do *not* ensure uniqueness of normal forms, since it
  -- is possible to build an HNF (∅ *x+ c) with c ≈ C*.0#.  In order to rule out this
  -- possibility not excluded by types, below we introduce an operation _guarded-*x+_
  -- which explicitly checks for this case and returns ∅ as a normal form.

------------------------------------------------------------------------
-- Equality and decidability

mutual
  data _HNF-≈_ : ∀ {n} → HNF n → HNF n → Set (r₁ ⊔ r₃) where
    ∅≈ : ∀ {n} → _HNF-≈_ {suc n} ∅ ∅
    *x+≈ : ∀ {n} {p₁ p₂ : HNF (suc n)} {c₁ c₂ : Normal n} →
           p₁ HNF-≈ p₂ → c₁ Normal-≈ c₂ → (p₁ *x+ c₁) HNF-≈ (p₂ *x+ c₂)

  data _Normal-≈_ : ∀ {n} → Normal n → Normal n → Set (r₁ ⊔ r₃) where
    con≈ : ∀ {c₁ c₂} → coeff≈ morphism c₁ c₂ → (con c₁) Normal-≈ (con c₂)
    poly≈ : ∀ {n} {p₁ p₂ : HNF (suc n)} → p₁ HNF-≈ p₂ → (poly p₁) Normal-≈ (poly p₂)

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
-- Ring operations on Horner normal forms

mutual
  HNF-0# : ∀ {n} → HNF (suc n)
  HNF-0# = ∅

  Normal-0# : ∀ {n} → Normal n
  Normal-0# {zero} = con C.0#
  Normal-0# {suc n} = poly HNF-0#

mutual
  HNF-1# : ∀ {n} → HNF (suc n)
  HNF-1# {n} = ∅ *x+ Normal-1# {n}

  Normal-1# : ∀ {n} → Normal n
  Normal-1# {zero} = con C.1#
  Normal-1# {suc n} = poly HNF-1#

_guarded-*x+_ : ∀ {n} → HNF (suc n) → Normal n → HNF (suc n)
(p₁ *x+ c') guarded-*x+ c = (p₁ *x+ c') *x+ c
∅ guarded-*x+ c with c Normal-≟ Normal-0# 
... | yes c≈0 = ∅
... | no c≉0 = ∅ *x+ c

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

_HNF-*x+_ : ∀ {n} → HNF (suc n) → HNF (suc n) → HNF (suc n)
p₁ HNF-*x+ (p₂ *x+ c) = (p₁ HNF-+ p₂) guarded-*x+ c
∅ HNF-*x+ ∅ = ∅
(p₁ *x+ c) HNF-*x+ ∅ = (p₁ *x+ c) *x+ Normal-0#

mutual
  HNF-actˡ : ∀ {n} → Normal n → HNF (suc n) → HNF (suc n)
  HNF-actˡ c ∅ = ∅
  HNF-actˡ c (p *x+ c') with c Normal-≟  Normal-0#
  ... | yes c≈0 = ∅
  ... | no c≉0  = HNF-actˡ c p *x+ (c Normal-* c') 

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

_Normal-^_ : ∀ {n} → Normal n → ℕ → Normal n
p Normal-^ zero = Normal-1#
p Normal-^ suc n = p Normal-* (p Normal-^ n)

------------------------------------------------------------------------
-- Evaluation and normalisation

mutual
  ⟦_⟧-HNF : ∀ {n} → HNF (suc n) → Carrier → Vec Carrier n → Carrier
  ⟦_⟧-HNF ∅ x xs = 0#
  ⟦_⟧-HNF (p *x+ c) x xs = ⟦ p ⟧-HNF x xs * x + ⟦ c ⟧-Normal xs

  ⟦_⟧-Normal : ∀ {n} → Normal n → Vec Carrier n → Carrier
  ⟦ con c ⟧-Normal [] = ⟦ c ⟧'
  ⟦ poly p ⟧-Normal (x ∷ xs) = ⟦ p ⟧-HNF x xs

con-HNF : ∀ {n} → Normal n → HNF (suc n)
con-HNF c with c Normal-≟ Normal-0#
... | yes _ = ∅
... | no _ = ∅ *x+ c

var-HNF : ∀ {n} → HNF (suc n)
var-HNF = (∅ *x+ Normal-1#) *x+ Normal-0#

normalise-con : ∀ {n} → C.Carrier → Normal n
normalise-con {zero} c = con c
normalise-con {suc n} c = poly (con-HNF (normalise-con {n} c))

normalise-var : ∀ {n} → Fin n → Normal n
normalise-var {zero} ()
normalise-var {suc n} zero = poly var-HNF
normalise-var {suc n} (suc i) = poly (con-HNF (normalise-var {n} i))

normalise : ∀ {n} → Polynomial n → Normal n
normalise (op [+] t₁ t₂) = normalise t₁ Normal-+ normalise t₂
normalise (op [*] t₁ t₂) = normalise t₁ Normal-* normalise t₂
normalise (con c) = normalise-con c
normalise (var i) = normalise-var i
normalise (t :^ k) = normalise t Normal-^ k
normalise (:- t) = Normal-‿ normalise t

⟦_⟧↓ : ∀ {n} → Polynomial n → Vec Carrier n → Carrier
⟦_⟧↓ p ρ = ⟦ normalise p ⟧-Normal ρ

------------------------------------------------------------------------
-- Correctness

-- Correctness (⟦_⟧↓ ≈ ⟦_⟧) follows from the fact that ⟦_⟧-Normal is a homomorphism.
-- To show this, we also need to show (due to the use of the guarded constructor) that
-- ⟦_⟧-Normal respects equality of normal forms.

mutual
  HNF-eval-cong : ∀ {n} {p₁ p₂ : HNF (suc n)} → p₁ HNF-≈ p₂ → ∀ x (xs : Vec Carrier n) →
                ⟦ p₁ ⟧-HNF x xs ≈ ⟦ p₂ ⟧-HNF x xs
  HNF-eval-cong ∅≈ x xs = refl
  HNF-eval-cong (*x+≈ p₁≈p₂ c₁≈c₂) x xs = +-cong (*-cong (HNF-eval-cong p₁≈p₂ x xs) refl) (Normal-eval-cong c₁≈c₂ xs)

  Normal-eval-cong : ∀ {n} {p₁ p₂ : Normal n} → p₁ Normal-≈ p₂ → ∀ (xs : Vec Carrier n) →
                ⟦ p₁ ⟧-Normal xs ≈ ⟦ p₂ ⟧-Normal xs
  Normal-eval-cong (con≈ c₁≈c₂) [] = c₁≈c₂
  Normal-eval-cong (poly≈ p₁≈p₂) (x ∷ xs) = HNF-eval-cong p₁≈p₂ x xs

Normal-eval-resp : ∀ {n} {p₁ p₂ : Normal n} → p₁ Normal-≈ p₂ → ∀ {xs : Vec Carrier n} {r} →
                ⟦ p₂ ⟧-Normal xs ≈ r → ⟦ p₁ ⟧-Normal xs ≈ r
Normal-eval-resp p₁≈p₂ {xs} [p₂]≈r = trans (Normal-eval-cong p₁≈p₂ xs) [p₂]≈r

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

Normal-0-homo : ∀ {n} xs → ⟦ Normal-0# {n} ⟧-Normal xs ≈ 0#
Normal-0-homo [] = 0-homo
Normal-0-homo (x ∷ xs) = refl

Normal-1-homo : ∀ {n} xs → ⟦ Normal-1# {n} ⟧-Normal xs ≈ 1#
Normal-1-homo [] = 1-homo
Normal-1-homo (x ∷ xs) = begin
  0# * x + ⟦ Normal-1# ⟧-Normal xs  ≈⟨ refl ⟨ +-cong ⟩ (Normal-1-homo xs) ⟩
  0# * x + 1#                         ≈⟨ lemma₈ _ _ ⟩
  1#                                  ∎

lemma-eval-c≈0 : ∀ {n} {c : Normal n} → c Normal-≈ Normal-0# → ∀ (xs : Vec Carrier n) →
               0# ≈ ⟦ c ⟧-Normal xs
lemma-eval-c≈0 c≈0 xs = sym $ Normal-eval-resp c≈0 (Normal-0-homo xs)

-- the guarded version of _*x+_ does not affect the result of evaluation, up to equality
lemma-eval-guarded : ∀ {n} → (p : HNF (suc n)) (c : Normal n) → ∀ x (xs : Vec Carrier n) →
      ⟦ p guarded-*x+ c ⟧-HNF x xs ≈ ⟦ p *x+ c ⟧-HNF x xs
lemma-eval-guarded (p *x+ c') c x xs = refl
lemma-eval-guarded ∅ c x xs with c Normal-≟ Normal-0#
... | yes c≈0 = begin
  0#                            ≈⟨ lemma-eval-c≈0 c≈0 xs ⟩
  ⟦ c ⟧-Normal xs             ≈⟨ sym $ lemma₈ _ _ ⟩
  0# * x + ⟦ c ⟧-Normal xs    ∎
... | no c≉0 = refl

mutual
 HNF-+-homo : ∀ {n} (p₁ p₂ : HNF (suc n)) x (xs : Vec Carrier n) →
     ⟦ p₁ HNF-+ p₂ ⟧-HNF x xs ≈ ⟦ p₁ ⟧-HNF x xs + ⟦ p₂ ⟧-HNF x xs
 HNF-+-homo ∅ p₂ x xs = sym (proj₁ +-identity _) 
 HNF-+-homo (p₁ *x+ x₁) ∅ x xs = sym (proj₂ +-identity _)
 HNF-+-homo (p₁ *x+ c₁) (p₂ *x+ c₂) x xs = begin
   ⟦ (p₁ HNF-+ p₂) guarded-*x+ (c₁ Normal-+ c₂) ⟧-HNF x xs 
      ≈⟨ lemma-eval-guarded (p₁ HNF-+ p₂) (c₁ Normal-+ c₂) x xs ⟩
   ⟦ p₁ HNF-+ p₂ ⟧-HNF x xs * x + ⟦ c₁ Normal-+ c₂ ⟧-Normal xs
      ≈⟨ (HNF-+-homo p₁ p₂ x xs ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ Normal-+-homo c₁ c₂ xs ⟩
       (⟦ p₁ ⟧-HNF x xs + ⟦ p₂ ⟧-HNF x xs) * x + (⟦ c₁ ⟧-Normal xs + ⟦ c₂ ⟧-Normal xs)
      ≈⟨ lemma₁ _ _ _ _ _ ⟩
   (⟦ p₁ ⟧-HNF x xs * x + ⟦ c₁ ⟧-Normal xs) + (⟦ p₂ ⟧-HNF x xs * x + ⟦ c₂ ⟧-Normal xs)
      ∎

 Normal-+-homo : ∀ {n} (p₁ p₂ : Normal n) (xs : Vec Carrier n) →
         ⟦ p₁ Normal-+ p₂ ⟧-Normal xs ≈ ⟦ p₁ ⟧-Normal xs + ⟦ p₂ ⟧-Normal xs
 Normal-+-homo (con c₁) (con c₂) [] = +-homo _ _
 Normal-+-homo (poly p₁) (poly p₂) (x ∷ xs) = HNF-+-homo p₁ p₂ x xs

HNF-*x+-homo : ∀ {n} (p₁ p₂ : HNF (suc n)) x (xs : Vec Carrier n) →
     ⟦ p₁ HNF-*x+ p₂ ⟧-HNF x xs ≈ ⟦ p₁ ⟧-HNF x xs * x + ⟦ p₂ ⟧-HNF x xs
HNF-*x+-homo p₁ (p₂ *x+ c₂) x xs = begin
  ⟦ (p₁ HNF-+ p₂) guarded-*x+ c₂ ⟧-HNF x xs
       ≈⟨ lemma-eval-guarded (p₁ HNF-+ p₂) c₂ x xs ⟩
  ⟦ p₁ HNF-+ p₂ ⟧-HNF x xs * x + ⟦ c₂ ⟧-Normal xs
       ≈⟨ (HNF-+-homo p₁ p₂ x xs ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ refl ⟩
  (⟦ p₁ ⟧-HNF x xs + ⟦ p₂ ⟧-HNF x xs) * x + ⟦ c₂ ⟧-Normal xs
       ≈⟨ lemma₀ _ _ _ _ ⟩
  ⟦ p₁ ⟧-HNF x xs * x + (⟦ p₂ ⟧-HNF x xs * x + ⟦ c₂ ⟧-Normal xs)
       ∎
HNF-*x+-homo ∅ ∅ x xs = sym $ lemma₈ _ _
HNF-*x+-homo (p₁ *x+ x) ∅ x₁ xs = +-cong refl (Normal-0-homo xs)

mutual
  HNF-actˡ-homo : ∀ {n} (c : Normal n) (p : HNF (suc n)) x (xs : Vec Carrier n) →
                 ⟦ HNF-actˡ c p ⟧-HNF x xs ≈ ⟦ c ⟧-Normal xs * ⟦ p ⟧-HNF x xs
  HNF-actˡ-homo c ∅ x xs = sym (proj₂ zero* _)
  HNF-actˡ-homo c (p *x+ c') x xs with c Normal-≟ Normal-0#
  ... | yes c≈0 = begin
    0#
       ≈⟨ sym (proj₁ zero* _) ⟩
    0# * (⟦ p ⟧-HNF x xs * x + ⟦ c' ⟧-Normal xs)
       ≈⟨ lemma-eval-c≈0 c≈0 xs ⟨ *-cong ⟩ refl ⟩
    ⟦ c ⟧-Normal xs  * (⟦ p ⟧-HNF x xs * x + ⟦ c' ⟧-Normal xs)
       ∎
  ... | no c≉0 = begin
    ⟦ HNF-actˡ c p ⟧-HNF x xs * x + ⟦ c Normal-* c' ⟧-Normal xs
       ≈⟨ (HNF-actˡ-homo c p x xs ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ Normal-*-homo c c' xs ⟩
    (⟦ c ⟧-Normal xs * ⟦ p ⟧-HNF x xs) * x + (⟦ c ⟧-Normal xs * ⟦ c' ⟧-Normal xs)
       ≈⟨ lemma₄ _ _ _ _ ⟩
    ⟦ c ⟧-Normal xs * (⟦ p ⟧-HNF x xs * x + ⟦ c' ⟧-Normal xs)
       ∎

  HNF-actʳ-homo : ∀ {n} (p : HNF (suc n)) (c : Normal n) x (xs : Vec Carrier n) →
                 ⟦ HNF-actʳ p c ⟧-HNF x xs ≈ ⟦ p ⟧-HNF x xs * ⟦ c ⟧-Normal xs
  HNF-actʳ-homo ∅ c x xs = sym (proj₁ zero* _)
  HNF-actʳ-homo (p *x+ c') c x xs with c Normal-≟ Normal-0#
  ... | yes c≈0 = begin
    0#
       ≈⟨ sym (proj₂ zero* _) ⟩
    (⟦ p ⟧-HNF x xs * x + ⟦ c' ⟧-Normal xs) * 0#
       ≈⟨ refl ⟨ *-cong ⟩ lemma-eval-c≈0 c≈0 xs ⟩
    (⟦ p ⟧-HNF x xs * x + ⟦ c' ⟧-Normal xs) * ⟦ c ⟧-Normal xs
       ∎
  ... | no c≉0 = begin
    ⟦ HNF-actʳ p c ⟧-HNF x xs * x + ⟦ c' Normal-* c ⟧-Normal xs
       ≈⟨ (HNF-actʳ-homo p c x xs ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ Normal-*-homo c' c xs ⟩
    (⟦ p ⟧-HNF x xs * ⟦ c ⟧-Normal xs) * x + (⟦ c' ⟧-Normal xs * ⟦ c ⟧-Normal xs)
       ≈⟨ lemma₃ _ _ _ _ ⟩
    (⟦ p ⟧-HNF x xs * x + ⟦ c' ⟧-Normal xs) * ⟦ c ⟧-Normal xs
       ∎

  HNF-*-homo : ∀ {n} (p₁ p₂ : HNF (suc n)) x (xs : Vec Carrier n) →
    ⟦ p₁ HNF-* p₂ ⟧-HNF x xs ≈ ⟦ p₁ ⟧-HNF x xs * ⟦ p₂ ⟧-HNF x xs
  HNF-*-homo ∅ p₂ x xs = sym (proj₁ zero* _)
  HNF-*-homo (p₁ *x+ c₁) ∅ x xs = sym $ proj₂ zero* _
  HNF-*-homo (p₁ *x+ c₁) (p₂ *x+ c₂) x xs = begin
    ⟦ ((p₁ HNF-* p₂) HNF-*x+ (HNF-actʳ p₁ c₂ HNF-+ HNF-actˡ c₁ p₂)) guarded-*x+
        (c₁ Normal-* c₂) ⟧-HNF x xs
       ≈⟨ lemma-eval-guarded ((p₁ HNF-* p₂) HNF-*x+ (HNF-actʳ p₁ c₂ HNF-+ HNF-actˡ c₁ p₂)) (c₁ Normal-* c₂) x xs ⟩
    ⟦(p₁ HNF-* p₂) HNF-*x+ (HNF-actʳ p₁ c₂ HNF-+ HNF-actˡ c₁ p₂) ⟧-HNF x xs * x +
    ⟦ c₁ Normal-* c₂ ⟧-Normal xs
       ≈⟨ (HNF-*x+-homo (p₁ HNF-* p₂) (HNF-actʳ p₁ c₂ HNF-+ HNF-actˡ c₁ p₂) x xs ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ Normal-*-homo c₁ c₂ xs ⟩
    (⟦ p₁ HNF-* p₂ ⟧-HNF x xs * x +  ⟦ HNF-actʳ p₁ c₂ HNF-+ HNF-actˡ c₁ p₂ ⟧-HNF x xs) * x +
    (⟦ c₁ ⟧-Normal xs * ⟦ c₂ ⟧-Normal xs)
       ≈⟨ ((HNF-*-homo p₁ p₂ x xs ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ (trans (HNF-+-homo (HNF-actʳ p₁ c₂) (HNF-actˡ c₁ p₂) x xs) (HNF-actʳ-homo p₁ c₂ x xs ⟨ +-cong ⟩ HNF-actˡ-homo c₁ p₂ x xs)) ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ refl ⟩
    ((⟦ p₁ ⟧-HNF x xs * ⟦ p₂ ⟧-HNF x xs) * x + ((⟦ p₁ ⟧-HNF x xs * ⟦ c₂ ⟧-Normal xs) +
     (⟦ c₁ ⟧-Normal xs * ⟦ p₂ ⟧-HNF x xs))) * x
    + (⟦ c₁ ⟧-Normal xs * ⟦ c₂ ⟧-Normal xs)
       ≈⟨ lemma₅′ _ _ _ _ _ ⟩
    (⟦ p₁ ⟧-HNF x xs * x + ⟦ c₁ ⟧-Normal xs) * (⟦ p₂ ⟧-HNF x xs * x + ⟦ c₂ ⟧-Normal xs)
       ∎

  Normal-*-homo : ∀ {n} (p₁ p₂ : Normal n) (xs : Vec Carrier n) →
                ⟦ p₁ Normal-* p₂ ⟧-Normal xs ≈ ⟦ p₁ ⟧-Normal xs * ⟦ p₂ ⟧-Normal xs
  Normal-*-homo (con c₁) (con c₂) [] = *-homo _ _
  Normal-*-homo (poly p₁) (poly p₂) (x ∷ xs) = HNF-*-homo p₁ p₂ x xs

mutual
  HNF-‿-homo : ∀ {n} (p : HNF (suc n)) x (xs : Vec Carrier n) →
              ⟦ HNF-‿ p ⟧-HNF x xs ≈ - ⟦ p ⟧-HNF x xs
  HNF-‿-homo p x xs =  begin
    ⟦ HNF-actˡ (Normal-‿ Normal-1#) p ⟧-HNF x xs
        ≈⟨ HNF-actˡ-homo (Normal-‿ Normal-1#) p x xs ⟩
    ⟦ Normal-‿ Normal-1# ⟧-Normal xs * ⟦ p ⟧-HNF x xs
        ≈⟨ trans (Normal-‿-homo Normal-1# xs) (-‿cong (Normal-1-homo xs)) ⟨ *-cong ⟩ refl ⟩
    - 1# * ⟦ p ⟧-HNF x xs
        ≈⟨ lemma₉ _ ⟩
    - ⟦ p ⟧-HNF x xs
        ∎

  Normal-‿-homo : ∀ {n} (p : Normal n) (xs : Vec Carrier n) →
                ⟦ Normal-‿ p ⟧-Normal xs ≈ - ⟦ p ⟧-Normal xs
  Normal-‿-homo (con c) [] = -‿homo _
  Normal-‿-homo (poly p) (x ∷ xs) = HNF-‿-homo p x xs

Normal-^-homo : ∀ {n} (p : Normal n) (k : ℕ) (xs : Vec Carrier n) →
                ⟦ p Normal-^ k ⟧-Normal xs ≈ ⟦ p ⟧-Normal xs ^ k
Normal-^-homo p zero xs = Normal-1-homo xs
Normal-^-homo p (suc k) xs = begin
  ⟦ p Normal-* (p Normal-^ k) ⟧-Normal xs         ≈⟨ Normal-*-homo p (p Normal-^ k) xs ⟩
  ⟦ p ⟧-Normal xs * ⟦ p Normal-^ k ⟧-Normal xs  ≈⟨ refl ⟨ *-cong ⟩ Normal-^-homo p k xs ⟩
  ⟦ p ⟧-Normal xs * (⟦ p ⟧-Normal xs ^ k)       ∎

con-HNF-homo : ∀ {n} → (c : Normal n) → ∀ x (xs : Vec Carrier n) →
          ⟦ con-HNF c ⟧-HNF x xs ≈ ⟦ c ⟧-Normal xs
con-HNF-homo c x xs with c Normal-≟ Normal-0#
... | yes c≈0 = lemma-eval-c≈0 c≈0 xs
... | no c≉0 = lemma₈ _ _

correct : ∀ {n} (p : Polynomial n) (xs : Vec Carrier n) → ⟦ p ⟧↓ xs ≈ ⟦ p ⟧ xs
correct (op [+] p₁ p₂) xs = trans (Normal-+-homo (normalise p₁) (normalise p₂) xs) (+-cong (correct p₁ xs) (correct p₂ xs)) 
correct (op [*] p₁ p₂) xs = trans (Normal-*-homo (normalise p₁) (normalise p₂) xs) (*-cong (correct p₁ xs) (correct p₂ xs)) 
correct (:- p) xs = trans (Normal-‿-homo (normalise p) xs) (-‿cong (correct p xs))
correct (p :^ k) xs = trans (Normal-^-homo (normalise p) k xs) (^-cong (correct p xs) (PropEq.refl {x = k}))
correct (con c) xs = correct-con c xs
  where
    correct-con : ∀ {n} (c : C.Carrier) (xs : Vec Carrier n) → 
                ⟦ normalise-con c ⟧-Normal xs ≈ ⟦ c ⟧'
    correct-con c [] = refl
    correct-con c (x ∷ xs) = trans (con-HNF-homo (normalise-con c) x xs) (correct-con c xs) 
correct (var i) xs = correct-var i xs
  where
    correct-var : ∀ {n} (i : Fin n) (xs : Vec Carrier n) → 
                  ⟦ normalise-var i ⟧-Normal xs ≈ lookup i xs
    correct-var () []
    correct-var zero (x ∷ xs) = begin
      (0# * x + ⟦ Normal-1# ⟧-Normal xs) * x + ⟦ Normal-0# ⟧-Normal xs
         ≈⟨ ((refl ⟨ +-cong ⟩ Normal-1-homo xs) ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ Normal-0-homo xs ⟩
      (0# * x + 1#) * x + 0#
         ≈⟨ lemma₇ _ ⟩
      x  ∎
    correct-var (suc i) (x ∷ xs) = trans (con-HNF-homo (normalise-var i) x xs) (correct-var i xs)

open Reflection setoid var ⟦_⟧ ⟦_⟧↓ correct
  public using (prove; solve) renaming (_⊜_ to _:=_)

------------------------------------------------------------------------
-- "Tactics"


-- For examples of how solve and _:=_ can be used to
-- semi-automatically prove ring equalities, see, for instance,
-- Data.Digit or Data.Nat.DivMod.
