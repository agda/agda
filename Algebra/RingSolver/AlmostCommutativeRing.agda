------------------------------------------------------------------------
-- Commutative semirings with some additional structure ("almost"
-- commutative rings), used by the ring solver
------------------------------------------------------------------------

module Algebra.RingSolver.AlmostCommutativeRing where

open import Relation.Binary
open import Algebra
open import Algebra.Structures
import Algebra.FunctionProperties as P
open import Algebra.Morphism
open import Data.Function

------------------------------------------------------------------------
-- Definitions

record IsAlmostCommutativeRing (s : Setoid)
                               (_+_ _*_ : P.Op₂ s)
                               (-_ : P.Op₁ s)
                               (0# 1# : Setoid.carrier s) : Set where
  open Setoid s
  field
    isCommutativeSemiring : IsCommutativeSemiring s _+_ _*_ 0# 1#
    -‿pres-≈              : -_ Preserves _≈_ ⟶ _≈_
    -‿*-distribˡ          : ∀ x y → (- x) * y ≈ - (x * y)
    -‿+-comm              : ∀ x y → (- x) + (- y) ≈ - (x + y)

  open IsCommutativeSemiring s isCommutativeSemiring public

record AlmostCommutativeRing : Set1 where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  field
    setoid                  : Setoid
    _+_                     : P.Op₂ setoid
    _*_                     : P.Op₂ setoid
    -_                      : P.Op₁ setoid
    0#                      : Setoid.carrier setoid
    1#                      : Setoid.carrier setoid
    isAlmostCommutativeRing :
      IsAlmostCommutativeRing setoid _+_ _*_ -_ 0# 1#

  open Setoid setoid public
  open IsAlmostCommutativeRing isAlmostCommutativeRing public

  commutativeSemiring : CommutativeSemiring
  commutativeSemiring =
    record { isCommutativeSemiring = isCommutativeSemiring }

  open CommutativeSemiring commutativeSemiring public
         using ( +-semigroup; +-monoid; +-commutativeMonoid
               ; *-semigroup; *-monoid; *-commutativeMonoid
               ; semiring
               )

  rawRing : RawRing
  rawRing = record
    { setoid = setoid
    ; _+_    = _+_
    ; _*_    = _*_
    ; -_     = -_
    ; 0#     = 0#
    ; 1#     = 1#
    }

------------------------------------------------------------------------
-- Homomorphisms

_-Raw-AlmostCommutative⟶_ : RawRing → AlmostCommutativeRing → Set
from -Raw-AlmostCommutative⟶ to = from -RawRing⟶ rawRing to
  where open AlmostCommutativeRing

-raw-almostCommutative⟶
  : ∀ r →
    AlmostCommutativeRing.rawRing r -Raw-AlmostCommutative⟶ r
-raw-almostCommutative⟶ r = record
  { ⟦_⟧    = id
  ; +-homo = λ _ _ → refl
  ; *-homo = λ _ _ → refl
  ; -‿homo = λ _ → refl
  ; 0-homo = refl
  ; 1-homo = refl
  }
  where open AlmostCommutativeRing r

------------------------------------------------------------------------
-- Conversions

-- Commutative rings are almost commutative rings.

fromCommutativeRing : CommutativeRing → AlmostCommutativeRing
fromCommutativeRing cr = record
  { isAlmostCommutativeRing = record
      { isCommutativeSemiring = isCommutativeSemiring
      ; -‿pres-≈              = -‿pres-≈
      ; -‿*-distribˡ          = -‿*-distribˡ
      ; -‿+-comm              = -‿∙-comm
      }
  }
  where
  open CommutativeRing cr
  import Algebra.Props.Ring as R; open R ring
  import Algebra.Props.AbelianGroup as AG; open AG +-abelianGroup

-- Commutative semirings can be viewed as almost commutative rings by
-- using identity as the "almost negation".

fromCommutativeSemiring : CommutativeSemiring → AlmostCommutativeRing
fromCommutativeSemiring cs = record
  { -_                      = id
  ; isAlmostCommutativeRing = record
      { isCommutativeSemiring = isCommutativeSemiring
      ; -‿pres-≈              = id
      ; -‿*-distribˡ          = λ _ _ → refl
      ; -‿+-comm              = λ _ _ → refl
      }
  }
  where open CommutativeSemiring cs
