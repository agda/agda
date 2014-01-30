
id : {A : Set} → A → A
id x = x

syntax id {A} x = x ∈ A

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Fin : Nat → Set where
  zero : Fin zero
  suc  : ∀ {n} → Fin n → Fin (suc n)

z = zero ∈ Fin zero

postulate
  hiddenFun : ∀ {f : Nat → Nat} {n} → Fin (f n)

syntax hiddenFun {λ x → y} = hide[ x ] y

z′ : Fin (suc zero)
z′ = hide[ x ] suc x
