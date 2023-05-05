{-# OPTIONS --cubical #-}

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Glue
open import Agda.Builtin.Cubical.Id
open import Agda.Builtin.Sigma
open import Agda.Primitive.Cubical
  renaming
    ( primIMax to _∨_
    ; primIMin to _∧_
    ; primINeg to ~_
    ; primComp to comp
    ; primHComp to primHComp
    ; primTransp to transp
    ; itIsOne to 1=1
    )

is-prop : Type → Type
is-prop A = (x y : A) → x ≡ y

is-set : Type → Type
is-set A = (x y : A) → is-prop (x ≡ y)

-- Basic boundary scavenging test:
is-prop→is-set : (A : Type) → is-prop A → is-set A
is-prop→is-set A ap x y p q i j = primHComp
  (λ { k (i = i0) → ap x (p j) k
     ; k (i = i1) → ap x (q j) k
     ; k (j = i0) → {!   !}
     ; k (j = i1) → {!   !}
     })
  {! x   !}
