postulate
  Nat : Set
  succ : Nat → Nat
  Le : Nat → Nat → Set
  Fin : Nat → Set
  low : ∀ {m n} → Le m n → Fin n → Fin m
  instance
    Le-refl : ∀ {n} → Le n n
    Le-succ : ∀ {m n} ⦃ _ : Le m n ⦄ → Le m (succ n)
  Chk1 : ∀ {n} → Fin n → Set
  Chk2 : ∀ {n} → Fin n → Fin n → Set
  Chk3 : ∀ {m n} ⦃ _ : Le m n ⦄ → Fin m → Fin n → Set

variable
  le : Le _ _
  X G : Fin _

postulate

  works : Chk1 G
        → Chk2 (low le G) X
        → Chk3 X G
  -- WAS: Instance argument got solved with `Le-refl`, which is not
  -- type-correct.
  -- SHOULD: result in a failed instance search

  fails : Chk2 (low le G) X
        → Chk3 X G
