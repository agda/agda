open import Agda.Builtin.Bool

bad : Bool → Bool
bad true = bad true
bad = λ _ → true
