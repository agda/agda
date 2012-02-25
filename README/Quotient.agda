------------------------------------------------------------------------
-- The Agda standard library
--
-- An example showing how the (very experimental) Quotient module can
-- be used: a definition of integers as pairs of natural numbers
------------------------------------------------------------------------

module README.Quotient where

open import Algebra
open import Data.Nat
import Data.Nat.Properties as Nat
open import Data.Product
import Level
open import Quotient
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

private
  module CS = CommutativeSemiring Nat.commutativeSemiring
open Nat.SemiringSolver
open P.≡-Reasoning

-- Integers defined as pairs of natural numbers quotiented in the
-- usual way.

ℤ-setoid : Setoid Level.zero Level.zero
ℤ-setoid = record
  { Carrier       = ℕ × ℕ
  ; _≈_           = _≈_
  ; isEquivalence = isEquivalence
  }
  where
  _≈_ = λ { (m+ , m-) (n+ , n-) → m+ + n- ≡ n+ + m- }

  abstract
    isEquivalence : IsEquivalence _≈_
    isEquivalence = record
      { refl  = λ {_} → P.refl
      ; sym   = λ p → P.sym p
      ; trans = λ { {m+ , m-}{n+ , n-}{z+ , z-} p q →
          Nat.cancel-+-left (n- + n+) (begin
            (n- + n+) + (m+ + z-)  ≡⟨ solve 4 (λ n- n+ m+ z- → (n- :+ n+) :+ (m+ :+ z-) :=
                                                               m+ :+ n- :+ (n+ :+ z-))
                                              P.refl n- n+ m+ z- ⟩
            m+ + n- + (n+ + z-)    ≡⟨ P.cong₂ _+_ p q ⟩
            n+ + m- + (z+ + n-)    ≡⟨ solve 4 (λ n+ m- z+ n- → n+ :+ m- :+ (z+ :+ n-) :=
                                                               (n- :+ n+) :+ (z+ :+ m-))
                                              P.refl n+ m- z+ n- ⟩
            (n- + n+) + (z+ + m-)  ∎) }
      }

ℤ : Set
ℤ = Quotient ℤ-setoid

-- Zero.

0ℤ : ℤ
0ℤ = [ 0 , 0 ]

-- Negation.

-_ : ℤ → ℤ
-_ =
  rec ℤ-setoid
      (λ { (m+ , m-) → [ m- , m+ ]})
      (λ { {m+ , m-} {n+ , n-} m+n-≡n+m- →
           [ begin
             m- + n+  ≡⟨ CS.+-comm m- n+ ⟩
             n+ + m-  ≡⟨ P.sym m+n-≡n+m- ⟩
             m+ + n-  ≡⟨ CS.+-comm m+ n- ⟩
             n- + m+  ∎
           ]-cong })

-- The negation of zero is zero.

-‿0 : - 0ℤ ≡ 0ℤ
-‿0 = P.refl

-- Negation is an involution.

-‿involution : ∀ i → - - i ≡ i
-‿involution =
  elim ℤ-setoid
       (λ i → - - i ≡ i)
       (λ _ → P.refl)
       (λ _ → P.proof-irrelevance _ _)
