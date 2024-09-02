{-# OPTIONS --safe --cubical --erasure #-}
module ReflectionGetDef where
open import Agda.Builtin.Bool
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Primitive

_>>=_ : {a b : Level} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

_>>_ : {a b : Level} {A : Set a} {B : Set b} → TC A → TC B → TC B
_>>_ = λ mx my → bindTC mx λ _ → my

refl : {a : Level} {A : Set a} {x : A} → x ≡ x
refl {_} {_} {x} _ = x

data S¹ : Set where
  base : S¹
  @0 loop : base ≡ base

macro
  erased? : Name → Term → TC ⊤
  erased? n hole = do
    data-cons d q ← getDefinition n
      where _ → typeError []
    `q ← quoteTC q
    unify hole `q

_ : erased? base ≡ quantity-ω
_ = refl

_ : erased? loop ≡ quantity-0
_ = refl
