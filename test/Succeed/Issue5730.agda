{-# OPTIONS --with-K -vtc.lhs.unify:50 #-}

open import Agda.Primitive        using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)

-- change `Set` to `Setω` breaks `seq`
data RecD  (I : Set) : Setω where
  ι : (i : I) → RecD I

data RecO {I J : Set} (e : I → J) : RecD I → RecD J → Setω where
  ι : (i : I) (j : J) (eq : e i ≡ j) → RecO e (ι i) (ι j)

seq : {I J K : Set} {e : I → J} {f : J → K} {D : RecD I} {E : RecD J} {F : RecD K}
  → RecO f E F → RecO e D E
  → RecO (λ i → f (e i)) D F
seq (ι _ _ refl) (ι _ _ refl) = ι _ _ refl
