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

{-
j : ∀ x → let (m , n) = x in m ≡ n
j x = {!!}
-}

data P (a {b} {{v}} c : Σ Nat (λ _ → Nat)) : Set where
  CON : a ≡ it → P a c

uncurry :
  {A : Set} {B : A → Set} {C : ∀ a → B a → Set} →
  ((a : A) (b : B a) → C a b) →
  ((a , b) : Σ A B)  → C a b
uncurry f = λ (a , b) → f a b

equal× : {A B : Set} (p q : Σ A (λ _ → B)) → Set
equal× = λ (a , b) (c , d) → Σ (a ≡ c) (λ _ → b ≡ d)

record WRAP : Set where
  constructor TTTTT
  field wrapped : Nat

id : WRAP → WRAP
id = λ x (let (TTTTT n) = x) → let (TTTTT n) = x in x

id' : WRAP → WRAP
id' = λ x@(TTTTT n) → x

id'' : WRAP → WRAP
id'' = λ (TTTTT n) → TTTTT n

shadowing : (p@(m , p) : Σ Nat (λ _ → Nat)) → Σ Nat (p ≡_)
shadowing = λ (_ , p) → p , refl
