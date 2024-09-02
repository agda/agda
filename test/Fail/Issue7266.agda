open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

P : Bool → Set
P true = ⊤
P false = Σ Bool λ _ → Bool

f : (A : Bool) → P A → P A
f true _ = f true tt
f false (true , _) = true , true
