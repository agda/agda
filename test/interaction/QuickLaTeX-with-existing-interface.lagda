\begin{code}
record Σ (A : Set) (B : A → Set) : Set where
  coinductive
  constructor c
  field
    proj₁ : A
    proj₂ : B proj₁

data D : Set where
  c : D

f : {A : Set} {B : A → Set} (x : A) → B x → Σ A B
f = c
\end{code}
