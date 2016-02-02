
postulate
  Bool : Set
  D    : Bool → Set
  f    : (a : Bool) → D a
  ⟦_⟧  : ∀ {a} → D a → Bool

record State : Set where
  field bool : Bool

open State {{...}}

postulate
  guard : {S : Set} → (S → Bool) → S

test : State
test = guard (λ σ → ⟦ f bool ⟧) -- doesn't work, used to work in agda 2.4
