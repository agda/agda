------------------------------------------------------------------------
-- Solver for commutative ring or semiring equalities
------------------------------------------------------------------------

-- Uses ideas from the Coq ring tactic. See "Proving Equalities in a
-- Commutative Ring Done Right in Coq" by Grégoire and Mahboubi. The
-- code below is not optimised like theirs, though.

open import Algebra.Packaged

module Algebra.RingSolver
  (coeff : BareRingoid)    -- Coefficient "ring".
  (r : AlmostCommRingoid)  -- Main "ring".
  (morphism : coeff -Bare-AlmostComm⟶ r)
  where

open import Relation.Binary
open import Logic
open import Data.Nat hiding (_*_) renaming (_+_ to _ℕ-+_)
open import Data.Fin
open import Data.Vec
open import Data.Function hiding (const)
open import Data.Product
open Π
import Relation.Binary.EqReasoning
import Algebra
import Algebra.Morphism as Morphism
import Algebra.Operations
import Algebra.Props.AlmostCommRing
import Algebra.RingSolver.Lemmas
private
  open module L = Algebra.RingSolver.Lemmas coeff r morphism
  open module R = AlmostCommRingoid r
  open module R = BareRingoid bare
  open module R = Algebra.Props.AlmostCommRing r
  open module S = Setoid setoid
  open module S = Equivalence equiv
  open module S = Preorder preorder
  open module S = Relation.Binary.EqReasoning (setoid⟶preSetoid setoid)
  open module R = Algebra setoid
  open module R = AlmostCommRing almostCommRing
  open module R = CommutativeSemiring commSemiring
  module I = Semiring semiring
  module A = Monoid (CommutativeMonoid.monoid I.+-monoid)
  module A = Semigroup A.semigroup
  module M = Semigroup (Monoid.semigroup I.*-monoid)
  open module R = Algebra.Operations semiringoid
  module C = BareRingoid coeff
  module C = Setoid C.setoid
  open module R = Morphism C.setoid setoid
  open module R = RingHomomorphism morphism renaming (⟦_⟧ to ⟦_⟧')

infix  9 _↑-NF :-_ ¬-NF_
infixr 9 _:^_ _^-NF_ _:↑_
infix  8 _*x _*x+_
infixl 8 _:*_ _*-NF_
infixl 7 _:+_ _+-NF_
infixl 5 _∷-NF_

------------------------------------------------------------------------
-- Polynomials

data Op : Set where
  [+] : Op
  [*] : Op

-- The polynomials are indexed over the number of variables.

data Polynomial (n : ℕ) : Set where
  op   : Op -> Polynomial n -> Polynomial n -> Polynomial n
  con  : C.carrier -> Polynomial n
  var  : Fin n -> Polynomial n
  _:^_ : Polynomial n -> ℕ -> Polynomial n
  :-_  : Polynomial n -> Polynomial n

-- Short-hand notation.

_:+_ : forall {n} -> Polynomial n -> Polynomial n -> Polynomial n
_:+_ = op [+]

_:*_ : forall {n} -> Polynomial n -> Polynomial n -> Polynomial n
_:*_ = op [*]

-- Semantics.

sem : Op -> Op₂
sem [+] = _+_
sem [*] = _*_

⟦_⟧_ : forall {n} -> Polynomial n -> Vec carrier n -> carrier
⟦ op o p₁ p₂ ⟧ ρ = ⟦ p₁ ⟧ ρ ⟨ sem o ⟩ ⟦ p₂ ⟧ ρ
⟦ con c ⟧      ρ = ⟦ c ⟧'
⟦ var x ⟧      ρ = lookup x ρ
⟦ p :^ n ⟧     ρ = ⟦ p ⟧ ρ ^ n
⟦ :- p ⟧       ρ = - ⟦ p ⟧ ρ

private

  -- Equality.

  _≛_ : forall {n} -> Polynomial n -> Polynomial n -> Set
  p₁ ≛ p₂ = forall {ρ} -> ⟦ p₁ ⟧ ρ ≈ ⟦ p₂ ⟧ ρ

  -- Reindexing.

  _:↑_ : forall {n} -> Polynomial n -> (m : ℕ) -> Polynomial (m ℕ-+ n)
  op o p₁ p₂ :↑ m = op o (p₁ :↑ m) (p₂ :↑ m)
  con c      :↑ m = con c
  var x      :↑ m = var (raise m x)
  (p :^ n)   :↑ m = (p :↑ m) :^ n
  (:- p)     :↑ m = :- (p :↑ m)

------------------------------------------------------------------------
-- Normal forms of polynomials

private

  -- The normal forms are indexed over
  -- * the number of variables in the polynomial, and
  -- * an equivalent polynomial.

  data Normal : (n : ℕ) -> Polynomial n -> Set where
    _∷-NF_ :  forall {n p₁ p₂}
           -> Normal n p₁ -> p₁ ≛ p₂ -> Normal n p₂
    con-NF :  (c : C.carrier) -> Normal 0 (con c)
    _↑-NF  :  forall {n p}
           -> Normal n p -> Normal (suc n) (p :↑ 1)
    _*x+_  :  forall {n p c}
           -> Normal (suc n) p -> Normal n c
           -> Normal (suc n) (p :* var fz :+ c :↑ 1)

  ⟦_⟧-NF_ : forall {n p} -> Normal n p -> Vec carrier n -> carrier
  ⟦ p ∷-NF _ ⟧-NF ρ       = ⟦ p ⟧-NF ρ
  ⟦ con-NF c ⟧-NF ρ       = ⟦ c ⟧'
  ⟦ p ↑-NF   ⟧-NF (x ∷ ρ) = ⟦ p ⟧-NF ρ
  ⟦ p *x+ c  ⟧-NF (x ∷ ρ) = ⟦ p ⟧-NF (x ∷ ρ) * x + ⟦ c ⟧-NF ρ

  con-NF⋆ : forall {n} -> (c : C.carrier) -> Normal n (con c)
  con-NF⋆ {zero}  c = con-NF c
  con-NF⋆ {suc _} c = con-NF⋆ c ↑-NF

  _*x : forall {n p} -> Normal (suc n) p -> Normal (suc n) (p :* var fz)
  p *x = p *x+ con-NF⋆ C.0# ∷-NF lemma₀ _

------------------------------------------------------------------------
-- Normalisation

private

  _+-NF_
    :  forall {n p₁ p₂}
    -> Normal n p₁ -> Normal n p₂
    -> Normal n (p₁ :+ p₂)
  (p₁ ∷-NF eq₁) +-NF (p₂ ∷-NF eq₂) = p₁ +-NF p₂                    ∷-NF eq₁   ⟨ A.•-pres-≈ ⟩ eq₂
  (p₁ ∷-NF eq)  +-NF p₂            = p₁ +-NF p₂                    ∷-NF eq    ⟨ A.•-pres-≈ ⟩ byDef
  p₁            +-NF (p₂ ∷-NF eq)  = p₁ +-NF p₂                    ∷-NF byDef ⟨ A.•-pres-≈ ⟩ eq
  con-NF c₁     +-NF con-NF c₂     = con-NF (C._+_ c₁ c₂)          ∷-NF +-homo _ _
  p₁ ↑-NF       +-NF p₂ ↑-NF       = (p₁ +-NF p₂) ↑-NF             ∷-NF byDef
  p₁ *x+ c₁     +-NF p₂ ↑-NF       = p₁ *x+ (c₁ +-NF p₂)           ∷-NF A.assoc _ _ _
  p₁ *x+ c₁     +-NF p₂ *x+ c₂     = (p₁ +-NF p₂) *x+ (c₁ +-NF c₂) ∷-NF lemma₁ _ _ _ _ _
  p₁ ↑-NF       +-NF p₂ *x+ c₂     = p₂ *x+ (p₁ +-NF c₂)           ∷-NF lemma₂ _ _ _

  -- TODO: The following function is terminating, but the termination
  -- checker cannot see it. Do something about this problem.

  _*-NF_
    :  forall {n p₁ p₂}
    -> Normal n p₁ -> Normal n p₂
    -> Normal n (p₁ :* p₂)
  (p₁ ∷-NF eq₁) *-NF (p₂ ∷-NF eq₂) = p₁ *-NF p₂                         ∷-NF eq₁   ⟨ M.•-pres-≈ ⟩ eq₂
  (p₁ ∷-NF eq)  *-NF p₂            = p₁ *-NF p₂                         ∷-NF eq    ⟨ M.•-pres-≈ ⟩ byDef
  p₁            *-NF (p₂ ∷-NF eq)  = p₁ *-NF p₂                         ∷-NF byDef ⟨ M.•-pres-≈ ⟩ eq
  con-NF c₁     *-NF con-NF c₂     = con-NF (C._*_ c₁ c₂)               ∷-NF *-homo _ _
  p₁ ↑-NF       *-NF p₂ ↑-NF       = (p₁ *-NF p₂) ↑-NF                  ∷-NF byDef
  (p₁ *x+ c₁)   *-NF p₂ ↑-NF       = (p₁ *-NF p₂ ↑-NF) *x+ (c₁ *-NF p₂) ∷-NF lemma₃ _ _ _ _
  p₁ ↑-NF       *-NF (p₂ *x+ c₂)   = (p₁ ↑-NF *-NF p₂) *x+ (p₁ *-NF c₂) ∷-NF lemma₄ _ _ _ _
  (p₁ *x+ c₁)   *-NF (p₂ *x+ c₂)   =
    (p₁ *-NF p₂) *x *x +-NF
    (p₁ *-NF c₂ ↑-NF +-NF c₁ ↑-NF *-NF p₂) *x+ (c₁ *-NF c₂)             ∷-NF lemma₅ _ _ _ _ _

  ¬-NF_ :  forall {n p} -> Normal n p -> Normal n (:- p)
  ¬-NF_ (p ∷-NF eq) = ¬-NF_ p ∷-NF ¬-pres-≈ eq
  ¬-NF_ (con-NF c)  = con-NF (C.-_ c) ∷-NF ¬-homo _
  ¬-NF_ (p ↑-NF)    = ¬-NF_ p ↑-NF
  ¬-NF_ (p *x+ c)   = ¬-NF_ p *x+ ¬-NF_ c ∷-NF lemma₆ _ _ _

  var-NF : forall {n} -> (i : Fin n) -> Normal n (var i)
  var-NF fz     = con-NF⋆ C.1# *x+ con-NF⋆ C.0# ∷-NF lemma₇ _
  var-NF (fs i) = var-NF i ↑-NF

  _^-NF_ : forall {n p} -> Normal n p -> (i : ℕ) -> Normal n (p :^ i)
  p ^-NF zero  = con-NF⋆ C.1#    ∷-NF 1-homo
  p ^-NF suc n = p *-NF p ^-NF n ∷-NF byDef

  normaliseOp
    :  (o : Op)
    -> forall {n p₁ p₂}
    -> Normal n p₁ -> Normal n p₂ -> Normal n (p₁ ⟨ op o ⟩ p₂)
  normaliseOp [+] = _+-NF_
  normaliseOp [*] = _*-NF_

  normalise : forall {n} (p : Polynomial n) -> Normal n p
  normalise (op o p₁ p₂) = normalise p₁ ⟨ normaliseOp o ⟩ normalise p₂
  normalise (con c)      = con-NF⋆ c
  normalise (var i)      = var-NF i
  normalise (p :^ n)     = normalise p ^-NF n
  normalise (:- p)       = ¬-NF normalise p

⟦_⟧↓_ : forall {n} -> Polynomial n -> Vec carrier n -> carrier
⟦ p ⟧↓ ρ = ⟦ normalise p ⟧-NF ρ

------------------------------------------------------------------------
-- Correctness

abstract
 private
  sem-pres-≈ : forall op -> sem op Preserves₂-≈
  sem-pres-≈ [+] = A.•-pres-≈
  sem-pres-≈ [*] = M.•-pres-≈

  raise-sem :  forall {n x} (p : Polynomial n) ρ
            -> ⟦ p :↑ 1 ⟧ (x ∷ ρ) ≈ ⟦ p ⟧ ρ
  raise-sem (op o p₁ p₂) ρ = raise-sem p₁ ρ ⟨ sem-pres-≈ o ⟩
                             raise-sem p₂ ρ
  raise-sem (con c)      ρ = byDef
  raise-sem (var x)      ρ = byDef
  raise-sem (p :^ n)     ρ = raise-sem p ρ ⟨ ^-pres-≈ ⟩ ≡-refl {x = n}
  raise-sem (:- p)       ρ = ¬-pres-≈ (raise-sem p ρ)

  nf-sound :  forall {n p} (nf : Normal n p) ρ
           -> ⟦ nf ⟧-NF ρ ≈ ⟦ p ⟧ ρ
  nf-sound (nf ∷-NF eq)       ρ       = nf-sound nf ρ ⟨ trans ⟩ eq
  nf-sound (con-NF c)         ρ       = byDef
  nf-sound (_↑-NF {p = p} nf) (x ∷ ρ) =
    nf-sound nf ρ ⟨ trans ⟩ sym (raise-sem p ρ)
  nf-sound (_*x+_ {c = c} nf₁ nf₂) (x ∷ ρ) =
    (nf-sound nf₁ (x ∷ ρ) ⟨ M.•-pres-≈ ⟩ byDef)
      ⟨ A.•-pres-≈ ⟩
    (nf-sound nf₂ ρ ⟨ trans ⟩ sym (raise-sem c ρ))

-- Completeness can presumably also be proved (i.e. the normal forms
-- should be unique, if the casts are ignored).

------------------------------------------------------------------------
-- "Tactic"

abstract

  prove :  forall {n} (ρ : Vec carrier n) p₁ p₂
        -> ⟦ p₁ ⟧↓ ρ ≈ ⟦ p₂ ⟧↓ ρ
        -> ⟦ p₁ ⟧  ρ ≈ ⟦ p₂ ⟧  ρ
  prove ρ p₁ p₂ eq =
    sym (nf-sound (normalise p₁) ρ)
      ⟨ trans ⟩
    eq
      ⟨ trans ⟩
    nf-sound (normalise p₂) ρ

-- For examples of how the function above can be used to
-- semi-automatically prove ring equalities, see
-- Prelude.RingSolver.Examples.
