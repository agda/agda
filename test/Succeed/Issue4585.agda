open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Reflection

id : ∀ {a} {A : Set a} → A → A
id x = x

macro
  my-macro : Term → TC ⊤
  my-macro goal = bindTC
    (getType (quote id))
    λ idType → bindTC
      (reduce idType)
      λ _ → returnTC _

fails? : ⊤
fails? = my-macro
