
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

data Maybe {a} (A : Set a) : Set a where
  just : A → Maybe A
  nothing : Maybe A

record RawRoutingAlgebra : Set₁ where
  field
    PathWeight : Set

module _ (A : RawRoutingAlgebra) where

  open RawRoutingAlgebra A

  PathWeight⁺ : Set
  PathWeight⁺ = Maybe (Σ PathWeight λ _ → Nat)

  data P : PathWeight⁺ → Set where
    [_] : ∀ {k} → snd k ≡ 0 → P (just k)

  badness : (r : PathWeight⁺) → P r → Set
  badness r [ refl ] = Nat
