
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit

postulate
  D : Set
  foo : ⦃ D ⦄ → Bool

it : {A : Set} → ⦃ A ⦄ → A
it ⦃ x ⦄ = x

data IsBool : Bool → Set where
  its-false : IsBool false
  its-true  : IsBool true

works₁ : ⦃ _ : D ⦄ → IsBool foo
works₁ with foo | Set       -- It works if you add more with abstractions
... | false | _ = its-false
... | true  | _ = its-true

works₂ : ⦃ _ : D ⦄ → IsBool foo
works₂ with foo ⦃ it ⦄      -- Or if you add the instance argument explicitly
... | false = its-false
... | true  = its-true

fails : ⦃ _ : D ⦄ → IsBool foo
fails with foo
... | false = its-false     -- false != foo because with abstraction failed
... | true  = its-true
