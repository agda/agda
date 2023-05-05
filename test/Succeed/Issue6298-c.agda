{-# OPTIONS --erased-cubical --erasure -WnoUnsupportedIndexedMatch #-}

open import Agda.Builtin.Sigma

const : {A : Set₁} {B : Set} → A → (B → A)
const x = λ _ → x

data ⊥ : Set where

I : Set
I = Σ ⊥ (const ⊥)

data C : @0 I → Set where
  c : ∀ {@0 x y} → C (x , y) → C (x , y)

data D : {@0 x : I} → @0 C x → Set where
  d : {@0 x : I} {@0 y : C x} → D y → D (c y)

P : {@0 x : I} → C x → Set
P (c x) = P x

f : {@0 x : I} (y : C x) → D y → P y
f (c x) (d y) = f x y
