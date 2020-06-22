open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

infix 1 Σ-syntax
Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

pair : Set → Set
pair A = Σ[ _ ∈ A ] A

diag : Set → Set
diag A = Σ[ p ∈ pair A ] fst p ≡ snd p

diag-pat : Set → Set
diag-pat A = Σ[ p@(x , y) ∈ pair A ] p ≡ (y , x)

-- WAS: parse error for p@(x , y)
-- WANT: success
