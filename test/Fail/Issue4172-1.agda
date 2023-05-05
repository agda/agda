{-# OPTIONS --cubical-compatible --erasure #-}

open import Agda.Builtin.Equality

subst-erased : {A : Set} {x y : A} (P : A → Set) → @0 x ≡ y → P x → P y
subst-erased P refl p = p
