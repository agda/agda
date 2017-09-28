
open import Agda.Builtin.Nat

record _×_ (A B : Set) : Set where
  constructor _,_
  field fst : A
        snd : B

open _×_

Δ : ∀ {A} → A → A × A
Δ x = x , x

foo : Nat → Nat
foo n = let x , y = Δ n in x + y

bar : Nat → Nat
bar n = let _!_ : Nat → Nat → Nat
            x ! y = 2 * x + y
        in n ! n
