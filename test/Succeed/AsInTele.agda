open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{p}} = p

f : (a {b} {{c}} : Nat) → Nat
f = λ a {b} → it

g : (a b@(c , d) (e , f) : Σ Nat (λ _ → Nat)) → Nat
g = λ a b@(c , d) x@(e , _) → f (fst a) {d} {{e}}

h : ∀ {a} (b@(c , d) : Σ Nat (λ _ → Nat)) → Nat
h {a} b = g a b b

i : ∀ a b → Nat
i a b = h {a} b

-- j : ∀ a b → Nat
-- j = λ a (e , f) → i a (f , e)

data P (a {b} {{v}} c : Σ Nat (λ _ → Nat)) : Set where
  CON : a ≡ it → P a c

uncurry :
  {A : Set} {B : A → Set} {C : ∀ a → B a → Set} →
  ((a : A) (b : B a) → C a b) →
  ((a , b) : Σ A B)  → C a b
uncurry f = λ (a , b) → f a b

equal× : {A B : Set} ((a , b) (c , d) : Σ A (λ _ → B)) → Set
equal× = λ (a , b) (c , d) → Σ (a ≡ c) (λ _ → b ≡ d)
