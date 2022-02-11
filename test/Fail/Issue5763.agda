
data Fun (A B : Set) : Set where
  fun : (A → B) → Fun A B

syntax fun (λ x → y) = fn x , y

foo : ∀ {A} → Fun A A → A
foo (fn x , y) = y
