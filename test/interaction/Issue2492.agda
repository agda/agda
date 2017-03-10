module Issue2492 where

open import Agda.Builtin.Nat

infix 0 _!
data Singleton {A : Set} : A → Set where
  _! : (a : A) → Singleton a

_ : Singleton 10
_ = {!!}
