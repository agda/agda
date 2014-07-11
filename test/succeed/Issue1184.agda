
postulate
  T : Set → Set
  X : Set

  Class : Set → Set
  member : ∀ {A} {{C : Class A}} → A → A

  instance
    iX : Class X
    iT : ∀ {A} {{CA : Class A}} → Class (T A)

-- Should get type Class (T X),
-- not {{_ : Class X}} → Class (T X)
iTX = iT {A = X}

-- Fails if not expanding instance argument in iTX
f : T X → T X
f = member
