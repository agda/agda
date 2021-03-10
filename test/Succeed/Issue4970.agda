
open import Agda.Builtin.Sigma renaming (fst to proj₁; snd to proj₂)
open import Agda.Builtin.Nat renaming (Nat to ℕ)

NEX : Set₁
NEX = Σ Set λ A → (ℕ → A)

variable
  A : NEX
  B : A .proj₁ → NEX

[Σ] : (A : NEX) → (B : A .proj₁ → NEX) → NEX
[Σ] A B .proj₁ = Σ (A .proj₁) λ x → B x .proj₁
[Σ] A B .proj₂ n = A .proj₂ n , B _ .proj₂ n

_[→]_ : (A B : NEX) → NEX
(A [→] B) .proj₁ = A .proj₁ → B .proj₁
(A [→] B) .proj₂ n x = B .proj₂ n

-- B.A is underdetermined and solved with (A .proj₁ , _snd) for a fresh meta
-- _snd : ℕ → A .proj₁, which is then generalized over. The bug was that _snd
-- turned into an explicit rather than implicit argument.
[π₁] : ([Σ] A B [→] A) .proj₁
[π₁] {A = A} {B = B} {snd} x = x .proj₁
