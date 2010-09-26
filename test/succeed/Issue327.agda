
module Issue327 where

open import Common.Prelude
open import Common.Reflect

_==_ : QName → QName → Bool
_==_ = primQNameEquality

postulate
  Dec : Bool → Set
  _≟_ : (x y : QName) → Dec (x == y)

Foo : Set₁
Foo with quote Foo ≟ quote Foo
... | _ = Set
