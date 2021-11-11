{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive
open import Agda.Primitive.Cubical
open import Agda.Builtin.Bool

variable
  a p         : Level
  A           : Set a
  P           : A → Set p
  x y : A

refl : x ≡ x
refl {x = x} = λ _ → x


data 𝕊¹ : Set where
  base : 𝕊¹
  loop : base ≡ base


g : Bool → I → 𝕊¹
g true i = base
g false i = loop i

_ : g false i0 ≡ base
_ = refl

_ : g true i0 ≡ base
_ = refl

-- non-unique solutions, should not solve either of the metas.
_ : g _ _ ≡ base
_ = refl


h : Bool → base ≡ base
h true = \ _ → base
h false = loop

_ : h false i0 ≡ base
_ = refl

_ : h true i0 ≡ base
_ = refl

-- non-unique solutions, should not solve either of the metas.
_ : h _ _ ≡ base
_ = refl
