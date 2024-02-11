open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Sigma

postulate
  ℕ : Type

data T (n : ℕ) : Type where
  conv : ∀ m → T m → T n

test : ∀ n → T n → Σ ℕ T
test n (conv m t) = let n' , t' = test m t in {!helper t'!}  -- C-c C-h

