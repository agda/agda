{-# OPTIONS --universe-polymorphism #-}

module Issue286 where

open import Common.Level

data Bool : Set where
  true false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

data _≡_ {ℓ : Level} {A : Set ℓ} : A → A → Set ℓ where
  refl : {a : A} → a ≡ a

{-# BUILTIN EQUALITY _≡_  #-}
{-# BUILTIN REFL     refl #-}

primitive
  primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

postulate String : Set

{-# BUILTIN STRING String #-}

primitive
  primStringEquality : String → String → Bool

data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

_≟_ : (s₁ s₂ : String) → Maybe (s₁ ≡ s₂)
s₁ ≟ s₂ with primStringEquality s₁ s₂
... | true  = just primTrustMe
... | false = nothing

_≟′_ : (s₁ s₂ : String) → Maybe (s₁ ≡ s₂)
s₁ ≟′ s₂ with s₁ ≟ s₂
s  ≟′ .s | just refl = just refl
_  ≟′ _  | nothing   = nothing

test : Maybe ("" ≡ "")
test = "" ≟′ ""

ok : test ≡ just refl
ok = refl
