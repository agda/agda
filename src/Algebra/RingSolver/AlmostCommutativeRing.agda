------------------------------------------------------------------------
-- The Agda standard library
--
-- Commutative semirings with some additional structure ("almost"
-- commutative rings), used by the ring solver
------------------------------------------------------------------------

module Algebra.RingSolver.AlmostCommutativeRing where

open import Relation.Binary
open import Algebra
open import Algebra.Structures
open import Algebra.FunctionProperties
import Algebra.Morphism as Morphism
open import Function
open import Level

------------------------------------------------------------------------
-- Definitions

record IsAlmostCommutativeRing
         {a ℓ} {A : Set a} (_≈_ : Rel A ℓ)
         (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    isCommutativeSemiring : IsCommutativeSemiring _≈_ _+_ _*_ 0# 1#
    -‿cong                : -_ Preserves _≈_ ⟶ _≈_
    -‿*-distribˡ          : ∀ x y → ((- x) * y)     ≈ (- (x * y))
    -‿+-comm              : ∀ x y → ((- x) + (- y)) ≈ (- (x + y))

  open IsCommutativeSemiring isCommutativeSemiring public

record AlmostCommutativeRing c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier                 : Set c
    _≈_                     : Rel Carrier ℓ
    _+_                     : Op₂ Carrier
    _*_                     : Op₂ Carrier
    -_                      : Op₁ Carrier
    0#                      : Carrier
    1#                      : Carrier
    isAlmostCommutativeRing :
      IsAlmostCommutativeRing _≈_ _+_ _*_ -_ 0# 1#

  open IsAlmostCommutativeRing isAlmostCommutativeRing public

  commutativeSemiring : CommutativeSemiring _ _
  commutativeSemiring =
    record { isCommutativeSemiring = isCommutativeSemiring }

  open CommutativeSemiring commutativeSemiring public
         using ( +-semigroup; +-monoid; +-commutativeMonoid
               ; *-semigroup; *-monoid; *-commutativeMonoid
               ; semiring
               )

  rawRing : RawRing _
  rawRing = record
    { _+_ = _+_
    ; _*_ = _*_
    ; -_  = -_
    ; 0#  = 0#
    ; 1#  = 1#
    }

------------------------------------------------------------------------
-- Homomorphisms

record _-Raw-AlmostCommutative⟶_
         {r₁ r₂ r₃}
         (From : RawRing r₁)
         (To : AlmostCommutativeRing r₂ r₃) : Set (r₁ ⊔ r₂ ⊔ r₃) where
  private
    module F = RawRing From
    module T = AlmostCommutativeRing To
  open Morphism.Definitions F.Carrier T.Carrier T._≈_
  field
    ⟦_⟧    : Morphism
    +-homo : Homomorphic₂ ⟦_⟧ F._+_ T._+_
    *-homo : Homomorphic₂ ⟦_⟧ F._*_ T._*_
    -‿homo : Homomorphic₁ ⟦_⟧ F.-_  T.-_
    0-homo : Homomorphic₀ ⟦_⟧ F.0#  T.0#
    1-homo : Homomorphic₀ ⟦_⟧ F.1#  T.1#

-raw-almostCommutative⟶
  : ∀ {r₁ r₂} (R : AlmostCommutativeRing r₁ r₂) →
    AlmostCommutativeRing.rawRing R -Raw-AlmostCommutative⟶ R
-raw-almostCommutative⟶ R = record
  { ⟦_⟧    = id
  ; +-homo = λ _ _ → refl
  ; *-homo = λ _ _ → refl
  ; -‿homo = λ _ → refl
  ; 0-homo = refl
  ; 1-homo = refl
  }
  where open AlmostCommutativeRing R

-- A homomorphism induces a notion of equivalence on the raw ring.

Induced-equivalence :
  ∀ {c₁ c₂ ℓ} {Coeff : RawRing c₁} {R : AlmostCommutativeRing c₂ ℓ} →
  Coeff -Raw-AlmostCommutative⟶ R → Rel (RawRing.Carrier Coeff) ℓ
Induced-equivalence {R = R} morphism a b = ⟦ a ⟧ ≈ ⟦ b ⟧
  where
  open AlmostCommutativeRing R
  open _-Raw-AlmostCommutative⟶_ morphism

------------------------------------------------------------------------
-- Conversions

-- Commutative rings are almost commutative rings.

fromCommutativeRing :
  ∀ {r₁ r₂} → CommutativeRing r₁ r₂ → AlmostCommutativeRing _ _
fromCommutativeRing CR = record
  { isAlmostCommutativeRing = record
      { isCommutativeSemiring = isCommutativeSemiring
      ; -‿cong                = -‿cong
      ; -‿*-distribˡ          = -‿*-distribˡ
      ; -‿+-comm              = ⁻¹-∙-comm
      }
  }
  where
  open CommutativeRing CR
  import Algebra.Properties.Ring as R; open R ring
  import Algebra.Properties.AbelianGroup as AG; open AG +-abelianGroup

-- Commutative semirings can be viewed as almost commutative rings by
-- using identity as the "almost negation".

fromCommutativeSemiring :
  ∀ {r₁ r₂} → CommutativeSemiring r₁ r₂ → AlmostCommutativeRing _ _
fromCommutativeSemiring CS = record
  { -_                      = id
  ; isAlmostCommutativeRing = record
      { isCommutativeSemiring = isCommutativeSemiring
      ; -‿cong                = id
      ; -‿*-distribˡ          = λ _ _ → refl
      ; -‿+-comm              = λ _ _ → refl
      }
  }
  where open CommutativeSemiring CS
