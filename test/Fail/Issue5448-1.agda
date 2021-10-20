{-# OPTIONS --without-K #-}

open import Agda.Builtin.Equality

subst :
  {A : Set} {x y : A}
  (@0 P : A → Set) → x ≡ y → P x → P y
subst P refl p = p
