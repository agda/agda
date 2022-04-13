{- Example by Andrew Pitts, 2016-05-23 -}

{-# OPTIONS --rewriting --cubical-compatible #-}

open import Agda.Builtin.Equality public

infix 6 I─_
postulate
  𝕀     : Set
  O     : 𝕀
  I     : 𝕀
  I─_   : 𝕀 → 𝕀

{-# BUILTIN REWRITE _≡_ #-}

postulate
  I─O≡I   :           I─ O     ≡ I

{-# REWRITE I─O≡I   #-}

data Pth (A : Set) : A → A → Set where
  path : (f : 𝕀 → A) → Pth A (f O) (f I)

infix 6 _at_
_at_ : {A : Set}{x y : A} → Pth A x y → 𝕀 → A
path f at i = f i

record Path (A : Set)(x y : A) : Set where
  field
    pth : Pth A x y
    feq : pth at O ≡ x
    seq : pth at I ≡ y

open Path public

{-# REWRITE feq #-}
{-# REWRITE seq #-}

infix 6 _′_
_′_ : {A : Set}{x y : A} → Path A x y → 𝕀 → A
p ′ i = pth p at i

fun2path : {A : Set}(f : 𝕀 → A) → Path A (f O) (f I)
pth (fun2path f) = path f
feq (fun2path f) = refl
seq (fun2path f) = refl

inv : {A : Set}{x y : A} → Path A x y → Path A y x
inv p = fun2path (λ i → p ′ (I─ i))
