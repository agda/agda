
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Reflection renaming (returnTC to return; bindTC to _>>=_)

_>>_ : ∀ {a} {b} {A : Set a} {B : Set b}
     → TC A → TC B → TC B
x >> y = x >>= λ _ → y

macro
  false-oh-no-actually-true : Term → TC ⊤
  false-oh-no-actually-true goal = do
    runSpeculative (do
      unify goal (con (quote false) [])
      return (tt , false))
    unify goal (con (quote true) [])

  false-yes-really-false : Term → TC ⊤
  false-yes-really-false goal =
    runSpeculative (do
      unify goal (con (quote false) [])
      return (tt , true))

test₁ : Bool
test₁ = false-oh-no-actually-true

_ : test₁ ≡ true
_ = refl

test₂ : Bool
test₂ = false-yes-really-false

_ : test₂ ≡ false
_ = refl
