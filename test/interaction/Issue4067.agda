postulate
  A  : Set
  F  : Set → Set
  P  : F A → Set
  id : F A → F A

f : (x : F A) → P x → P x
f _ p = p

⟨_⟩ : F A → F A
⟨ x ⟩ = x

{-# NOINLINE ⟨_⟩ #-}

record R (F : Set → Set) : Set₁ where
  field
    g : F A → F A

open R ⦃ … ⦄

postulate
  instance
    r : R F

-- In all three cases below the ⟨_⟩ should be retained in the goal type.

works : (x : F A) → P x
works x = f ⟨ x ⟩ {!!}

also-works : (x : F A) → P (id x)
also-works x = f (id ⟨ x ⟩) {!!}

fails : (x : F A) → P (g x)
fails x = f (g ⟨ x ⟩) {!!}
