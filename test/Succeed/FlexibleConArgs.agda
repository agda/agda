{-# OPTIONS --cubical #-}

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path


refl : ∀ {a}{A : Set a} {x : A} → x ≡ x
refl {x = x} = \ i → x


data Sphere : Set where
  base : Sphere
  surf : PathP (\ i → PathP (\ j → Sphere) base base) (\ _ → base) (\ _ → base)


elim : (D : Sphere → Set) → (b : D base) →
       (s : PathP (\ i → PathP (\ j → D (surf i j)) b b) refl refl) →
       -- the type for the refl is unified with D (surf i0 j), where j is not in scope.
       -- Agda should recognize that "j" is flexible since it goes away by endpoint reduction.
       (x : Sphere) → D x
elim D b s base = b
elim D b s (surf i j) = s i j
