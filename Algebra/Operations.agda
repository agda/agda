------------------------------------------------------------------------
-- Some defined operations
------------------------------------------------------------------------

open import Algebra.Packaged

module Algebra.Operations (s : Semiringoid) where

open import Relation.Binary
open import Relation.Binary.Conversion
open import Relation.Binary.PropositionalEquality
open import Logic
open import Data.Function
open import Data.Nat using (zero; suc; ℕ)
import Algebra
import Relation.Binary.EqReasoning
private
  open module R = Semiringoid s
  open module A = Algebra setoid
  open module S = Setoid setoid
  open module S = Equivalence equiv
  open module S = Preorder preorder
  module R = Semiring semiring
  module A = CommutativeMonoid R.+-monoid
  module A = Monoid A.monoid
  module A = Semigroup A.semigroup
  module M = Monoid R.*-monoid
  module M = Semigroup M.semigroup
  open module S = Relation.Binary.EqReasoning (setoid⟶preSetoid setoid)

------------------------------------------------------------------------
-- Operations

-- Multiplication by natural number.

_×_ : ℕ -> carrier -> carrier
zero  × x = 0#
suc n × x = x + (n × x)

-- Exponentiation.

_^_ : carrier -> ℕ -> carrier
x ^ zero  = 1#
x ^ suc n = x * (x ^ n)

------------------------------------------------------------------------
-- Some properties

abstract

  ×-pres-≈ : _×_ Preserves₂ _≡_ , _≈_ , _≈_
  ×-pres-≈ {n} {n'} {x} {x'} n≡n' x≈x' =
    n × x
            ≃⟨ refl $ ≡-cong (\n -> n × x) n≡n' ⟩
    n' × x
            ≃⟨ ×-pres-≈ʳ n' x≈x' ⟩
    n' × x'
            ∎
    where
    ×-pres-≈ʳ : forall n -> (_×_ n) Preserves-≈
    ×-pres-≈ʳ zero    x≈x' = byDef
    ×-pres-≈ʳ (suc n) x≈x' = x≈x' ⟨ A.•-pres-≈ ⟩ ×-pres-≈ʳ n x≈x'

  ^-pres-≈ : _^_ Preserves₂ _≈_ , _≡_ , _≈_
  ^-pres-≈ {x} {x'} {n} {n'} x≈x' n≡n' =
    x ^ n
            ≃⟨ refl $ ≡-cong (_^_ x) n≡n' ⟩
    x ^ n'
            ≃⟨ ^-pres-≈ˡ n' x≈x' ⟩
    x' ^ n'
            ∎
    where
    ^-pres-≈ˡ : forall n -> (\x -> x ^ n) Preserves-≈
    ^-pres-≈ˡ zero    x≈x' = byDef
    ^-pres-≈ˡ (suc n) x≈x' = x≈x' ⟨ M.•-pres-≈ ⟩ ^-pres-≈ˡ n x≈x'
