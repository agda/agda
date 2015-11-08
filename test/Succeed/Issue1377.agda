data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Zero : Nat → Set where
  instance
    isZero : Zero zero

data NonZero : Nat → Set where
  instance
    isSuc : ∀ {n : Nat} → NonZero (suc n)

pred : ∀ t {{_ : NonZero t}} → Nat
pred ._ {{isSuc {n}}} = n

test : Nat
test = pred (suc zero)

data Test (x : Nat) : Set where
  here  : {{_ : Zero x}} → Test x
  there : {{nz : NonZero x}} → Test (pred x) → Test x

broken : Test (suc zero)
broken = there here
