postulate
  ∞  : ∀ {a} (A : Set a) → Set a
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}

sharp1 : Set → ∞ Set
sharp1 = ♯_ -- ok

{-# BUILTIN FLAT     ♭  #-}

sharp2 : Set → ∞ Set
sharp2 A = ♯ A -- ok

sharp3 : Set → ∞ Set
sharp3 = ♯_ -- not ok for some reason
