------------------------------------------------------------------------
-- The Agda standard library
--
-- Solver for commutative ring or semiring equalities
------------------------------------------------------------------------

-- Uses ideas from the Coq ring tactic. See "Proving Equalities in a
-- Commutative Ring Done Right in Coq" by Grégoire and Mahboubi. The
-- code below is not optimised like theirs, though (in particular, our
-- Horner normal forms are not sparse).

open import Algebra
open import Algebra.RingSolver.AlmostCommutativeRing

open import Relation.Binary

module Algebra.RingSolver
  {r₁ r₂ r₃}
  (Coeff : RawRing r₁)               -- Coefficient "ring".
  (R : AlmostCommutativeRing r₂ r₃)  -- Main "ring".
  (morphism : Coeff -Raw-AlmostCommutative⟶ R)
  (_coeff≟_ : Decidable (Induced-equivalence morphism))
  where

import Algebra.RingSolver.Lemmas as L; open L Coeff R morphism
private module C = RawRing Coeff
open AlmostCommutativeRing R renaming (zero to zero*)
import Algebra.FunctionProperties as P; open P _≈_
open import Algebra.Morphism
open _-Raw-AlmostCommutative⟶_ morphism renaming (⟦_⟧ to ⟦_⟧′)
import Algebra.Operations as Ops; open Ops semiring

open import Relation.Binary
open import Relation.Nullary
import Relation.Binary.EqReasoning as EqR; open EqR setoid
import Relation.Binary.PropositionalEquality as PropEq
import Relation.Binary.Reflection as Reflection

open import Data.Empty
open import Data.Product
open import Data.Nat.Base as Nat using (ℕ; suc; zero)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec
open import Function
open import Level using (_⊔_)

infix  9 :-_ -H_ -N_
infixr 9 _:^_ _^N_
infix  8 _*x+_ _*x+HN_ _*x+H_
infixl 8 _:*_ _*N_ _*H_ _*NH_ _*HN_
infixl 7 _:+_ _:-_ _+H_ _+N_
infix  4 _≈H_ _≈N_

------------------------------------------------------------------------
-- Polynomials

data Op : Set where
  [+] : Op
  [*] : Op

-- The polynomials are indexed by the number of variables.

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
⟦ con c      ⟧ ρ = ⟦ c ⟧′
⟦ var x      ⟧ ρ = lookup x ρ
⟦ p :^ n     ⟧ ρ = ⟦ p ⟧ ρ ^ n
⟦ :- p       ⟧ ρ = - ⟦ p ⟧ ρ

------------------------------------------------------------------------
-- Normal forms of polynomials

-- A univariate polynomial of degree d,
--
--     p = a_d x^d + a_{d-1}x^{d-1} + … + a_0,
--
-- is represented in Horner normal form by
--
--     p = ((a_d x + a_{d-1})x + …)x + a_0.
--
-- Note that Horner normal forms can be represented as lists, with the
-- empty list standing for the zero polynomial of degree "-1".
--
-- Given this representation of univariate polynomials over an
-- arbitrary ring, polynomials in any number of variables over the
-- ring C can be represented via the isomorphisms
--
--     C[] ≅ C
--
-- and
--
--     C[X_0,...X_{n+1}] ≅ C[X_0,...,X_n][X_{n+1}].

mutual

  -- The polynomial representations are indexed by the polynomial's
  -- degree.

  data HNF : ℕ → Set r₁ where
    ∅     : ∀ {n} → HNF (suc n)
    _*x+_ : ∀ {n} → HNF (suc n) → Normal n → HNF (suc n)

  data Normal : ℕ → Set r₁ where
    con  : C.Carrier → Normal zero
    poly : ∀ {n} → HNF (suc n) → Normal (suc n)

  -- Note that the data types above do /not/ ensure uniqueness of
  -- normal forms: the zero polynomial of degree one can be
  -- represented using both ∅ and ∅ *x+ con C.0#.

mutual

  -- Semantics.

  ⟦_⟧H : ∀ {n} → HNF (suc n) → Vec Carrier (suc n) → Carrier
  ⟦ ∅       ⟧H _       = 0#
  ⟦ p *x+ c ⟧H (x ∷ ρ) = ⟦ p ⟧H (x ∷ ρ) * x + ⟦ c ⟧N ρ

  ⟦_⟧N : ∀ {n} → Normal n → Vec Carrier n → Carrier
  ⟦ con c  ⟧N _ = ⟦ c ⟧′
  ⟦ poly p ⟧N ρ = ⟦ p ⟧H ρ

------------------------------------------------------------------------
-- Equality and decidability

mutual

  -- Equality.

  data _≈H_ : ∀ {n} → HNF n → HNF n → Set (r₁ ⊔ r₃) where
    ∅     : ∀ {n} → _≈H_ {suc n} ∅ ∅
    _*x+_ : ∀ {n} {p₁ p₂ : HNF (suc n)} {c₁ c₂ : Normal n} →
            p₁ ≈H p₂ → c₁ ≈N c₂ → (p₁ *x+ c₁) ≈H (p₂ *x+ c₂)

  data _≈N_ : ∀ {n} → Normal n → Normal n → Set (r₁ ⊔ r₃) where
    con  : ∀ {c₁ c₂} → ⟦ c₁ ⟧′ ≈ ⟦ c₂ ⟧′ → con c₁ ≈N con c₂
    poly : ∀ {n} {p₁ p₂ : HNF (suc n)} → p₁ ≈H p₂ → poly p₁ ≈N poly p₂

mutual

  -- Equality is decidable.

  _≟H_ : ∀ {n} → Decidable (_≈H_ {n = n})
  ∅           ≟H ∅           = yes ∅
  ∅           ≟H (_ *x+ _)   = no λ()
  (_ *x+ _)   ≟H ∅           = no λ()
  (p₁ *x+ c₁) ≟H (p₂ *x+ c₂) with p₁ ≟H p₂ | c₁ ≟N c₂
  ... | yes p₁≈p₂ | yes c₁≈c₂ = yes (p₁≈p₂ *x+ c₁≈c₂)
  ... | _         | no  c₁≉c₂ = no  λ { (_ *x+ c₁≈c₂) → c₁≉c₂ c₁≈c₂ }
  ... | no  p₁≉p₂ | _         = no  λ { (p₁≈p₂ *x+ _) → p₁≉p₂ p₁≈p₂ }

  _≟N_ : ∀ {n} → Decidable (_≈N_ {n = n})
  con c₁ ≟N con c₂ with c₁ coeff≟ c₂
  ... | yes c₁≈c₂ = yes (con c₁≈c₂)
  ... | no  c₁≉c₂ = no  λ { (con c₁≈c₂) → c₁≉c₂ c₁≈c₂}
  poly p₁ ≟N poly p₂ with p₁ ≟H p₂
  ... | yes p₁≈p₂ = yes (poly p₁≈p₂)
  ... | no  p₁≉p₂ = no  λ { (poly p₁≈p₂) → p₁≉p₂ p₁≈p₂ }

mutual

  -- The semantics respect the equality relations defined above.

  ⟦_⟧H-cong : ∀ {n} {p₁ p₂ : HNF (suc n)} →
              p₁ ≈H p₂ → ∀ ρ → ⟦ p₁ ⟧H ρ ≈ ⟦ p₂ ⟧H ρ
  ⟦ ∅               ⟧H-cong _       = refl
  ⟦ p₁≈p₂ *x+ c₁≈c₂ ⟧H-cong (x ∷ ρ) =
    (⟦ p₁≈p₂ ⟧H-cong (x ∷ ρ) ⟨ *-cong ⟩ refl)
      ⟨ +-cong ⟩
    ⟦ c₁≈c₂ ⟧N-cong ρ

  ⟦_⟧N-cong :
    ∀ {n} {p₁ p₂ : Normal n} →
    p₁ ≈N p₂ → ∀ ρ → ⟦ p₁ ⟧N ρ ≈ ⟦ p₂ ⟧N ρ
  ⟦ con c₁≈c₂  ⟧N-cong _ = c₁≈c₂
  ⟦ poly p₁≈p₂ ⟧N-cong ρ = ⟦ p₁≈p₂ ⟧H-cong ρ

------------------------------------------------------------------------
-- Ring operations on Horner normal forms

-- Zero.

0H : ∀ {n} → HNF (suc n)
0H = ∅

0N : ∀ {n} → Normal n
0N {zero}  = con C.0#
0N {suc n} = poly 0H

mutual

  -- One.

  1H : ∀ {n} → HNF (suc n)
  1H {n} = ∅ *x+ 1N {n}

  1N : ∀ {n} → Normal n
  1N {zero}  = con C.1#
  1N {suc n} = poly 1H

-- A simplifying variant of _*x+_.

_*x+HN_ : ∀ {n} → HNF (suc n) → Normal n → HNF (suc n)
(p *x+ c′) *x+HN c = (p *x+ c′) *x+ c
∅          *x+HN c with c ≟N 0N
... | yes c≈0 = ∅
... | no  c≉0 = ∅ *x+ c

mutual

  -- Addition.

  _+H_ : ∀ {n} → HNF (suc n) → HNF (suc n) → HNF (suc n)
  ∅           +H p           = p
  p           +H ∅           = p
  (p₁ *x+ c₁) +H (p₂ *x+ c₂) = (p₁ +H p₂) *x+HN (c₁ +N c₂)

  _+N_ : ∀ {n} → Normal n → Normal n → Normal n
  con c₁  +N con c₂  = con (c₁ C.+ c₂)
  poly p₁ +N poly p₂ = poly (p₁ +H p₂)

-- Multiplication.

_*x+H_ : ∀ {n} → HNF (suc n) → HNF (suc n) → HNF (suc n)
p₁         *x+H (p₂ *x+ c) = (p₁ +H p₂) *x+HN c
∅          *x+H ∅          = ∅
(p₁ *x+ c) *x+H ∅          = (p₁ *x+ c) *x+ 0N

mutual

  _*NH_ : ∀ {n} → Normal n → HNF (suc n) → HNF (suc n)
  c *NH ∅          = ∅
  c *NH (p *x+ c′) with c ≟N 0N
  ... | yes c≈0 = ∅
  ... | no  c≉0 = (c *NH p) *x+ (c *N c′)

  _*HN_ : ∀ {n} → HNF (suc n) → Normal n → HNF (suc n)
  ∅          *HN c = ∅
  (p *x+ c′) *HN c with c ≟N 0N
  ... | yes c≈0 = ∅
  ... | no  c≉0 = (p *HN c) *x+ (c′ *N c)

  _*H_ : ∀ {n} → HNF (suc n) → HNF (suc n) → HNF (suc n)
  ∅           *H _           = ∅
  (_ *x+ _)   *H ∅           = ∅
  (p₁ *x+ c₁) *H (p₂ *x+ c₂) =
    ((p₁ *H p₂) *x+H (p₁ *HN c₂ +H c₁ *NH p₂)) *x+HN (c₁ *N c₂)

  _*N_ : ∀ {n} → Normal n → Normal n → Normal n
  con c₁  *N con c₂  = con (c₁ C.* c₂)
  poly p₁ *N poly p₂ = poly (p₁ *H p₂)

-- Exponentiation.

_^N_ : ∀ {n} → Normal n → ℕ → Normal n
p ^N zero  = 1N
p ^N suc n = p *N (p ^N n)

mutual

  -- Negation.

  -H_ : ∀ {n} → HNF (suc n) → HNF (suc n)
  -H p = (-N 1N) *NH p

  -N_ : ∀ {n} → Normal n → Normal n
  -N con c  = con (C.- c)
  -N poly p = poly (-H p)

------------------------------------------------------------------------
-- Normalisation

normalise-con : ∀ {n} → C.Carrier → Normal n
normalise-con {zero}  c = con c
normalise-con {suc n} c = poly (∅ *x+HN normalise-con c)

normalise-var : ∀ {n} → Fin n → Normal n
normalise-var zero    = poly ((∅ *x+ 1N) *x+ 0N)
normalise-var (suc i) = poly (∅ *x+HN normalise-var i)

normalise : ∀ {n} → Polynomial n → Normal n
normalise (op [+] t₁ t₂) = normalise t₁ +N normalise t₂
normalise (op [*] t₁ t₂) = normalise t₁ *N normalise t₂
normalise (con c)        = normalise-con c
normalise (var i)        = normalise-var i
normalise (t :^ k)       = normalise t ^N k
normalise (:- t)         = -N normalise t

-- Evaluation after normalisation.

⟦_⟧↓ : ∀ {n} → Polynomial n → Vec Carrier n → Carrier
⟦ p ⟧↓ ρ = ⟦ normalise p ⟧N ρ

------------------------------------------------------------------------
-- Homomorphism lemmas

0N-homo : ∀ {n} ρ → ⟦ 0N {n} ⟧N ρ ≈ 0#
0N-homo []      = 0-homo
0N-homo (x ∷ ρ) = refl

-- If c is equal to 0N, then c is semantically equal to 0#.

0≈⟦0⟧ : ∀ {n} {c : Normal n} → c ≈N 0N → ∀ ρ → 0# ≈ ⟦ c ⟧N ρ
0≈⟦0⟧ {c = c} c≈0 ρ = sym (begin
  ⟦ c  ⟧N ρ  ≈⟨ ⟦ c≈0 ⟧N-cong ρ ⟩
  ⟦ 0N ⟧N ρ  ≈⟨ 0N-homo ρ ⟩
  0#         ∎)

1N-homo : ∀ {n} ρ → ⟦ 1N {n} ⟧N ρ ≈ 1#
1N-homo []      = 1-homo
1N-homo (x ∷ ρ) = begin
  0# * x + ⟦ 1N ⟧N ρ  ≈⟨ refl ⟨ +-cong ⟩ 1N-homo ρ ⟩
  0# * x + 1#         ≈⟨ lemma₆ _ _ ⟩
  1#                  ∎

-- _*x+HN_ is equal to _*x+_.

*x+HN≈*x+ : ∀ {n} (p : HNF (suc n)) (c : Normal n) →
            ∀ ρ → ⟦ p *x+HN c ⟧H ρ ≈ ⟦ p *x+ c ⟧H ρ
*x+HN≈*x+ (p *x+ c′) c ρ       = refl
*x+HN≈*x+ ∅          c (x ∷ ρ) with c ≟N 0N
... | yes c≈0 = begin
  0#                 ≈⟨ 0≈⟦0⟧ c≈0 ρ ⟩
  ⟦ c ⟧N ρ           ≈⟨ sym $ lemma₆ _ _ ⟩
  0# * x + ⟦ c ⟧N ρ  ∎
... | no c≉0 = refl

∅*x+HN-homo : ∀ {n} (c : Normal n) x ρ →
              ⟦ ∅ *x+HN c ⟧H (x ∷ ρ) ≈ ⟦ c ⟧N ρ
∅*x+HN-homo c x ρ with c ≟N 0N
... | yes c≈0 = 0≈⟦0⟧ c≈0 ρ
... | no  c≉0 = lemma₆ _ _

mutual

  +H-homo : ∀ {n} (p₁ p₂ : HNF (suc n)) →
            ∀ ρ → ⟦ p₁ +H p₂ ⟧H ρ ≈ ⟦ p₁ ⟧H ρ + ⟦ p₂ ⟧H ρ
  +H-homo ∅           p₂          ρ       = sym (proj₁ +-identity _)
  +H-homo (p₁ *x+ x₁) ∅           ρ       = sym (proj₂ +-identity _)
  +H-homo (p₁ *x+ c₁) (p₂ *x+ c₂) (x ∷ ρ) = begin
    ⟦ (p₁ +H p₂) *x+HN (c₁ +N c₂) ⟧H (x ∷ ρ)                           ≈⟨ *x+HN≈*x+ (p₁ +H p₂) (c₁ +N c₂) (x ∷ ρ) ⟩

    ⟦ p₁ +H p₂ ⟧H (x ∷ ρ) * x + ⟦ c₁ +N c₂ ⟧N ρ                        ≈⟨ (+H-homo p₁ p₂ (x ∷ ρ) ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ +N-homo c₁ c₂ ρ ⟩

    (⟦ p₁ ⟧H (x ∷ ρ) + ⟦ p₂ ⟧H (x ∷ ρ)) * x + (⟦ c₁ ⟧N ρ + ⟦ c₂ ⟧N ρ)  ≈⟨ lemma₁ _ _ _ _ _ ⟩

    (⟦ p₁ ⟧H (x ∷ ρ) * x + ⟦ c₁ ⟧N ρ) +
    (⟦ p₂ ⟧H (x ∷ ρ) * x + ⟦ c₂ ⟧N ρ)                                  ∎

  +N-homo : ∀ {n} (p₁ p₂ : Normal n) →
            ∀ ρ → ⟦ p₁ +N p₂ ⟧N ρ ≈ ⟦ p₁ ⟧N ρ + ⟦ p₂ ⟧N ρ
  +N-homo (con c₁)  (con c₂)  _ = +-homo _ _
  +N-homo (poly p₁) (poly p₂) ρ = +H-homo p₁ p₂ ρ

*x+H-homo :
  ∀ {n} (p₁ p₂ : HNF (suc n)) x ρ →
  ⟦ p₁ *x+H p₂ ⟧H (x ∷ ρ) ≈
  ⟦ p₁ ⟧H (x ∷ ρ) * x + ⟦ p₂ ⟧H (x ∷ ρ)
*x+H-homo ∅         ∅ _ _ = sym $ lemma₆ _ _
*x+H-homo (p *x+ c) ∅ x ρ = begin
  ⟦ p *x+ c ⟧H (x ∷ ρ) * x + ⟦ 0N ⟧N ρ  ≈⟨ refl ⟨ +-cong ⟩ 0N-homo ρ ⟩
  ⟦ p *x+ c ⟧H (x ∷ ρ) * x + 0#         ∎
*x+H-homo p₁         (p₂ *x+ c₂) x ρ = begin
  ⟦ (p₁ +H p₂) *x+HN c₂ ⟧H (x ∷ ρ)                         ≈⟨ *x+HN≈*x+ (p₁ +H p₂) c₂ (x ∷ ρ) ⟩
  ⟦ p₁ +H p₂ ⟧H (x ∷ ρ) * x + ⟦ c₂ ⟧N ρ                    ≈⟨ (+H-homo p₁ p₂ (x ∷ ρ) ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ refl ⟩
  (⟦ p₁ ⟧H (x ∷ ρ) + ⟦ p₂ ⟧H (x ∷ ρ)) * x + ⟦ c₂ ⟧N ρ      ≈⟨ lemma₀ _ _ _ _ ⟩
  ⟦ p₁ ⟧H (x ∷ ρ) * x + (⟦ p₂ ⟧H (x ∷ ρ) * x + ⟦ c₂ ⟧N ρ)  ∎

mutual

  *NH-homo :
    ∀ {n} (c : Normal n) (p : HNF (suc n)) x ρ →
    ⟦ c *NH p ⟧H (x ∷ ρ) ≈ ⟦ c ⟧N ρ * ⟦ p ⟧H (x ∷ ρ)
  *NH-homo c ∅          x ρ = sym (proj₂ zero* _)
  *NH-homo c (p *x+ c′) x ρ with c ≟N 0N
  ... | yes c≈0 = begin
    0#                                            ≈⟨ sym (proj₁ zero* _) ⟩
    0# * (⟦ p ⟧H (x ∷ ρ) * x + ⟦ c′ ⟧N ρ)         ≈⟨ 0≈⟦0⟧ c≈0 ρ ⟨ *-cong ⟩ refl ⟩
    ⟦ c ⟧N ρ  * (⟦ p ⟧H (x ∷ ρ) * x + ⟦ c′ ⟧N ρ)  ∎
  ... | no c≉0 = begin
    ⟦ c *NH p ⟧H (x ∷ ρ) * x + ⟦ c *N c′ ⟧N ρ                 ≈⟨ (*NH-homo c p x ρ ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ *N-homo c c′ ρ ⟩
    (⟦ c ⟧N ρ * ⟦ p ⟧H (x ∷ ρ)) * x + (⟦ c ⟧N ρ * ⟦ c′ ⟧N ρ)  ≈⟨ lemma₃ _ _ _ _ ⟩
    ⟦ c ⟧N ρ * (⟦ p ⟧H (x ∷ ρ) * x + ⟦ c′ ⟧N ρ)               ∎

  *HN-homo :
    ∀ {n} (p : HNF (suc n)) (c : Normal n) x ρ →
    ⟦ p *HN c ⟧H (x ∷ ρ) ≈ ⟦ p ⟧H (x ∷ ρ) * ⟦ c ⟧N ρ
  *HN-homo ∅          c x ρ = sym (proj₁ zero* _)
  *HN-homo (p *x+ c′) c x ρ with c ≟N 0N
  ... | yes c≈0 = begin
    0#                                           ≈⟨ sym (proj₂ zero* _) ⟩
    (⟦ p ⟧H (x ∷ ρ) * x + ⟦ c′ ⟧N ρ) * 0#        ≈⟨ refl ⟨ *-cong ⟩ 0≈⟦0⟧ c≈0 ρ ⟩
    (⟦ p ⟧H (x ∷ ρ) * x + ⟦ c′ ⟧N ρ) * ⟦ c ⟧N ρ  ∎
  ... | no c≉0 = begin
    ⟦ p *HN c ⟧H (x ∷ ρ) * x + ⟦ c′ *N c ⟧N ρ                 ≈⟨ (*HN-homo p c x ρ ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ *N-homo c′ c ρ ⟩
    (⟦ p ⟧H (x ∷ ρ) * ⟦ c ⟧N ρ) * x + (⟦ c′ ⟧N ρ * ⟦ c ⟧N ρ)  ≈⟨ lemma₂ _ _ _ _ ⟩
    (⟦ p ⟧H (x ∷ ρ) * x + ⟦ c′ ⟧N ρ) * ⟦ c ⟧N ρ               ∎

  *H-homo : ∀ {n} (p₁ p₂ : HNF (suc n)) →
            ∀ ρ → ⟦ p₁ *H p₂ ⟧H ρ ≈ ⟦ p₁ ⟧H ρ * ⟦ p₂ ⟧H ρ
  *H-homo ∅           p₂          ρ       = sym $ proj₁ zero* _
  *H-homo (p₁ *x+ c₁) ∅           ρ       = sym $ proj₂ zero* _
  *H-homo (p₁ *x+ c₁) (p₂ *x+ c₂) (x ∷ ρ) = begin
    ⟦ ((p₁ *H p₂) *x+H ((p₁ *HN c₂) +H (c₁ *NH p₂))) *x+HN
      (c₁ *N c₂) ⟧H (x ∷ ρ)                                              ≈⟨ *x+HN≈*x+ ((p₁ *H p₂) *x+H ((p₁ *HN c₂) +H (c₁ *NH p₂)))
                                                                                      (c₁ *N c₂) (x ∷ ρ) ⟩
    ⟦ (p₁ *H p₂) *x+H
      ((p₁ *HN c₂) +H (c₁ *NH p₂)) ⟧H (x ∷ ρ) * x +
    ⟦ c₁ *N c₂ ⟧N ρ                                                      ≈⟨ (*x+H-homo (p₁ *H p₂) ((p₁ *HN c₂) +H (c₁ *NH p₂)) x ρ
                                                                               ⟨ *-cong ⟩
                                                                             refl)
                                                                              ⟨ +-cong ⟩
                                                                            *N-homo c₁ c₂ ρ ⟩
    (⟦ p₁ *H p₂ ⟧H (x ∷ ρ) * x +
     ⟦ (p₁ *HN c₂) +H (c₁ *NH p₂) ⟧H (x ∷ ρ)) * x +
    ⟦ c₁ ⟧N ρ * ⟦ c₂ ⟧N ρ                                                ≈⟨ (((*H-homo p₁ p₂ (x ∷ ρ) ⟨ *-cong ⟩ refl)
                                                                                ⟨ +-cong ⟩
                                                                              (+H-homo (p₁ *HN c₂) (c₁ *NH p₂) (x ∷ ρ)))
                                                                               ⟨ *-cong ⟩
                                                                             refl)
                                                                              ⟨ +-cong ⟩
                                                                            refl ⟩
    (⟦ p₁ ⟧H (x ∷ ρ) * ⟦ p₂ ⟧H (x ∷ ρ) * x +
     (⟦ p₁ *HN c₂ ⟧H (x ∷ ρ) + ⟦ c₁ *NH p₂ ⟧H (x ∷ ρ))) * x +
    ⟦ c₁ ⟧N ρ * ⟦ c₂ ⟧N ρ                                                ≈⟨ ((refl ⟨ +-cong ⟩ (*HN-homo p₁ c₂ x ρ ⟨ +-cong ⟩ *NH-homo c₁ p₂ x ρ))
                                                                               ⟨ *-cong ⟩
                                                                             refl)
                                                                              ⟨ +-cong ⟩
                                                                            refl ⟩
    (⟦ p₁ ⟧H (x ∷ ρ) * ⟦ p₂ ⟧H (x ∷ ρ) * x +
     (⟦ p₁ ⟧H (x ∷ ρ) * ⟦ c₂ ⟧N ρ + ⟦ c₁ ⟧N ρ * ⟦ p₂ ⟧H (x ∷ ρ))) * x +
    (⟦ c₁ ⟧N ρ * ⟦ c₂ ⟧N ρ)                                              ≈⟨ lemma₄ _ _ _ _ _ ⟩

    (⟦ p₁ ⟧H (x ∷ ρ) * x + ⟦ c₁ ⟧N ρ) *
    (⟦ p₂ ⟧H (x ∷ ρ) * x + ⟦ c₂ ⟧N ρ)                                    ∎

  *N-homo : ∀ {n} (p₁ p₂ : Normal n) →
            ∀ ρ → ⟦ p₁ *N p₂ ⟧N ρ ≈ ⟦ p₁ ⟧N ρ * ⟦ p₂ ⟧N ρ
  *N-homo (con c₁)  (con c₂)  _ = *-homo _ _
  *N-homo (poly p₁) (poly p₂) ρ = *H-homo p₁ p₂ ρ

^N-homo : ∀ {n} (p : Normal n) (k : ℕ) →
          ∀ ρ → ⟦ p ^N k ⟧N ρ ≈ ⟦ p ⟧N ρ ^ k
^N-homo p zero    ρ = 1N-homo ρ
^N-homo p (suc k) ρ = begin
  ⟦ p *N (p ^N k) ⟧N ρ       ≈⟨ *N-homo p (p ^N k) ρ ⟩
  ⟦ p ⟧N ρ * ⟦ p ^N k ⟧N ρ   ≈⟨ refl ⟨ *-cong ⟩ ^N-homo p k ρ ⟩
  ⟦ p ⟧N ρ * (⟦ p ⟧N ρ ^ k)  ∎

mutual

  -H‿-homo : ∀ {n} (p : HNF (suc n)) →
             ∀ ρ → ⟦ -H p ⟧H ρ ≈ - ⟦ p ⟧H ρ
  -H‿-homo p (x ∷ ρ) = begin
    ⟦ (-N 1N) *NH p ⟧H (x ∷ ρ)     ≈⟨ *NH-homo (-N 1N) p x ρ ⟩
    ⟦ -N 1N ⟧N ρ * ⟦ p ⟧H (x ∷ ρ)  ≈⟨ trans (-N‿-homo 1N ρ) (-‿cong (1N-homo ρ)) ⟨ *-cong ⟩ refl ⟩
    - 1# * ⟦ p ⟧H (x ∷ ρ)          ≈⟨ lemma₇ _ ⟩
    - ⟦ p ⟧H (x ∷ ρ)               ∎

  -N‿-homo : ∀ {n} (p : Normal n) →
             ∀ ρ → ⟦ -N p ⟧N ρ ≈ - ⟦ p ⟧N ρ
  -N‿-homo (con c)  _ = -‿homo _
  -N‿-homo (poly p) ρ = -H‿-homo p ρ

------------------------------------------------------------------------
-- Correctness

correct-con : ∀ {n} (c : C.Carrier) (ρ : Vec Carrier n) →
              ⟦ normalise-con c ⟧N ρ ≈ ⟦ c ⟧′
correct-con c []      = refl
correct-con c (x ∷ ρ) = begin
  ⟦ ∅ *x+HN normalise-con c ⟧H (x ∷ ρ)  ≈⟨ ∅*x+HN-homo (normalise-con c) x ρ ⟩
  ⟦ normalise-con c ⟧N ρ            ≈⟨ correct-con c ρ ⟩
  ⟦ c ⟧′                                   ∎

correct-var : ∀ {n} (i : Fin n) →
              ∀ ρ → ⟦ normalise-var i ⟧N ρ ≈ lookup i ρ
correct-var ()      []
correct-var (suc i) (x ∷ ρ) = begin
  ⟦ ∅ *x+HN normalise-var i ⟧H (x ∷ ρ)  ≈⟨ ∅*x+HN-homo (normalise-var i) x ρ ⟩
  ⟦ normalise-var i ⟧N ρ                ≈⟨ correct-var i ρ ⟩
  lookup i ρ                            ∎
correct-var zero (x ∷ ρ) = begin
  (0# * x + ⟦ 1N ⟧N ρ) * x + ⟦ 0N ⟧N ρ  ≈⟨ ((refl ⟨ +-cong ⟩ 1N-homo ρ) ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ 0N-homo ρ ⟩
  (0# * x + 1#) * x + 0#                ≈⟨ lemma₅ _ ⟩
  x                                     ∎

correct : ∀ {n} (p : Polynomial n) → ∀ ρ → ⟦ p ⟧↓ ρ ≈ ⟦ p ⟧ ρ
correct (op [+] p₁ p₂) ρ = begin
  ⟦ normalise p₁ +N normalise p₂ ⟧N ρ  ≈⟨ +N-homo (normalise p₁) (normalise p₂) ρ ⟩
  ⟦ p₁ ⟧↓ ρ + ⟦ p₂ ⟧↓ ρ                ≈⟨ correct p₁ ρ ⟨ +-cong ⟩ correct p₂ ρ ⟩
  ⟦ p₁ ⟧ ρ + ⟦ p₂ ⟧ ρ                  ∎
correct (op [*] p₁ p₂) ρ = begin
  ⟦ normalise p₁ *N normalise p₂ ⟧N ρ  ≈⟨ *N-homo (normalise p₁) (normalise p₂) ρ ⟩
  ⟦ p₁ ⟧↓ ρ * ⟦ p₂ ⟧↓ ρ                ≈⟨ correct p₁ ρ ⟨ *-cong ⟩ correct p₂ ρ ⟩
  ⟦ p₁ ⟧ ρ * ⟦ p₂ ⟧ ρ                  ∎
correct (con c)  ρ = correct-con c ρ
correct (var i)  ρ = correct-var i ρ
correct (p :^ k) ρ = begin
  ⟦ normalise p ^N k ⟧N ρ  ≈⟨ ^N-homo (normalise p) k ρ ⟩
  ⟦ p ⟧↓ ρ ^ k             ≈⟨ correct p ρ ⟨ ^-cong ⟩ PropEq.refl {x = k} ⟩
  ⟦ p ⟧ ρ ^ k              ∎
correct (:- p) ρ = begin
  ⟦ -N normalise p ⟧N ρ  ≈⟨ -N‿-homo (normalise p) ρ ⟩
  - ⟦ p ⟧↓ ρ             ≈⟨ -‿cong (correct p ρ) ⟩
  - ⟦ p ⟧ ρ              ∎

------------------------------------------------------------------------
-- "Tactics"

open Reflection setoid var ⟦_⟧ ⟦_⟧↓ correct public
  using (prove; solve) renaming (_⊜_ to _:=_)

-- For examples of how solve and _:=_ can be used to
-- semi-automatically prove ring equalities, see, for instance,
-- Data.Digit or Data.Nat.DivMod.
