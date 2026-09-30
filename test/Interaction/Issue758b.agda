
data Nat : Set where
  O : Nat
  S : Nat → Nat

syntax S x = suc x

test : Nat → Nat
test _ = suc O

syntax lim (λ n → m) = limit n at m

data lim (f : Nat → Nat) : Set where

syntax foo (λ _ → n) = const-foo n

postulate
  foo : (Nat → Nat) → Nat
