postulate
  T : Set → Set
  _>>=_ : ∀ {A B} → T A → (A → T B) → T B

argh : ∀ {A} → T A → T A
argh ta = do
  f x ← ta
  {!!}
