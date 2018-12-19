
module _ where

open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

record Id (A : Set) : Set where
  field id : A → A

open Id {{...}}

postulate
  T    : {A : Set} → A → Set
  cong : ∀ {A B : Set} (f : A → B) {x} → T x → T (f x)

  X : Set
  lem  : (x : X) → T x

instance
  IdX : Id X
  IdX .id n = n

macro
  follows-from : Term → Term → TC ⊤
  follows-from prf hole = do
    typeError (termErr prf ∷ [])

loops : (x : X) → T x
loops x =
  follows-from (cong id (lem x))
