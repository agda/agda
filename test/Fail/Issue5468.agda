{-# OPTIONS --erased-cubical #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Cubical.Path
open import Agda.Primitive
open import Agda.Primitive.Cubical

private
  variable
    a p : Level
    A   : Set a
    P   : A → Set p
    x y : A

refl : x ≡ x
refl {x = x} = λ _ → x

subst : (P : A → Set p) → x ≡ y → P x → P y
subst P eq p = primTransp (λ i → P (eq i)) i0 p

record Erased (@0 A : Set a) : Set a where
  constructor [_]
  field
    @0 erased : A

[]-cong : {@0 A : Set a} {@0 x y : A} → @0 x ≡ y → [ x ] ≡ [ y ]
[]-cong eq = λ i → [ eq i ]

data Box : @0 Set → Set₁ where
  [_] : ∀ {A} → A → Box A

unbox : ∀ {@0 A} → Box A → A
unbox [ x ] = x

postulate
  @0 not : Bool ≡ Bool

should-be-true : Bool
should-be-true =
  unbox (subst (λ ([ A ]) → Box A) ([]-cong refl) [ true ])

should-be-false : Bool
should-be-false =
  unbox (subst (λ ([ A ]) → Box A) ([]-cong not) [ true ])
