open import Agda.Builtin.Equality
open import Agda.Primitive

record R a : Set (lsuc a) where
  field
    P : {A : Set a} → A → A → Set a

r : ∀ ℓ → R ℓ
R.P (r _) = _≡_

postulate
  cong  : ∀ {a b} {A : Set a} {B : Set b} {x y : A}
          (f : A → B) → R.P (r a) x y → R.P (r b) (f x) (f y)
  magic : ∀ {a} {A : Set a} {x y : A} (z : A) → y ≡ z → x ≡ z

record Raw-monad {f : Level → Level}
                 (M : ∀ {ℓ} → Set ℓ → Set (f ℓ)) ℓ₁ ℓ₂ :
                 Set (f ℓ₁ ⊔ f ℓ₂ ⊔ lsuc (ℓ₁ ⊔ ℓ₂)) where
  infixl 5 _>>=_
  field
    return : {A : Set ℓ₁} → A → M A
    _>>=_  : {A : Set ℓ₁} {B : Set ℓ₂} → M A → (A → M B) → M B

module Raw-monad⁺
  {f : Level → Level}
  {M : ∀ {ℓ} → Set ℓ → Set (f ℓ)}
  (m : ∀ {ℓ₁ ℓ₂} → Raw-monad M ℓ₁ ℓ₂)
  where

  private
    module M′ {ℓ₁ ℓ₂} = Raw-monad (m {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂})
  open M′ public using (_>>=_)

  return : ∀ {a} {A : Set a} → A → M A
  return = M′.return {ℓ₂ = lzero}

open Raw-monad⁺ ⦃ … ⦄ public

record Monad⁻ {f : Level → Level}
              (M : ∀ {ℓ} → Set ℓ → Set (f ℓ))
              ⦃ raw-monad : ∀ {ℓ₁ ℓ₂} → Raw-monad M ℓ₁ ℓ₂ ⦄
              ℓ₁ ℓ₂ ℓ₃ :
              Set (f ℓ₁ ⊔ f ℓ₂ ⊔ f ℓ₃ ⊔ lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    associativity :
      {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} →
      (x : M A) (f : A → M B) (g : B → M C) →
      x >>= (λ x → f x >>= g) ≡ x >>= f >>= g

module Monad⁻⁺
  {f : Level → Level}
  {M : ∀ {ℓ} → Set ℓ → Set (f ℓ)}
  ⦃ raw-monad : ∀ {ℓ₁ ℓ₂} → Raw-monad M ℓ₁ ℓ₂ ⦄
  (m : ∀ {ℓ₁ ℓ₂ ℓ₃} → Monad⁻ M ℓ₁ ℓ₂ ℓ₃)
  where

  private
    module M′ {ℓ₁ ℓ₂ ℓ₃} = Monad⁻ (m {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {ℓ₃ = ℓ₃})
  open M′ public

open Monad⁻⁺ ⦃ … ⦄ public

data Maybe {a} (A : Set a) : Set a where
  nothing : Maybe A
  just    : A → Maybe A

postulate
  maybe : ∀ {a b} {A : Set a} {B : Maybe A → Set b} →
          ((x : A) → B (just x)) → B nothing → (x : Maybe A) → B x

record MaybeT {ℓ}
              (f : Level → Level)
              (M : Set ℓ → Set (f ℓ))
              (A : Set ℓ) : Set (f ℓ) where
  constructor wrap
  field
    run : M (Maybe A)

open MaybeT

instance

  transformʳ :
    ∀ {ℓ₁ ℓ₂}
    {f : Level → Level}
    {M : ∀ {ℓ} → Set ℓ → Set (f ℓ)} →
    ⦃ raw-monad : ∀ {ℓ₁ ℓ₂} → Raw-monad M ℓ₁ ℓ₂ ⦄ →
    Raw-monad (MaybeT f M) ℓ₁ ℓ₂
  run (Raw-monad.return transformʳ x)   = return (just x)
  run (Raw-monad._>>=_  transformʳ x f) =
    run x >>= maybe (λ x → run (f x)) (return nothing)

transformᵐ :
  {f : Level → Level}
  {M : ∀ {ℓ} → Set ℓ → Set (f ℓ)}
  ⦃ raw-monad : ∀ {ℓ₁ ℓ₂} → Raw-monad M ℓ₁ ℓ₂ ⦄
  ⦃ monad : ∀ {ℓ₁ ℓ₂ ℓ₃} → Monad⁻ M ℓ₁ ℓ₂ ℓ₃ ⦄ →
  Monad⁻ (MaybeT f M) lzero lzero lzero
Monad⁻.associativity transformᵐ x f g = cong wrap (
  magic ((run x >>= maybe (λ x → run (f x)) (return nothing)) >>=
         maybe (λ x → run (g x)) (return nothing))
        (associativity _ _ _))

-- WAS: rejected in 2.6.0 with
-- No instance of type Raw-monad _M_345 ℓ₁ ℓ₂ was found in scope.

-- Should succeed.
