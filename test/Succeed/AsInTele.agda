open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{p}} = p

f : (a {b} {{c}} : Nat) → Nat
f = λ a {b} → it

g : (a b@(c , d) (e , f) : Σ Nat (λ _ → Nat)) → Nat
g a = λ b@(c , d) (e , f) → 0

h : ∀ {a b@(c , d)} → Nat
h {a} {b} = g a b b

i : ∀ a b@(c , d) → Nat
i a b = h {a} {b}

j : ∀ a (e , f) → Nat
j = λ a b@(e , f) → i a b
