
module _ where

open import Common.Prelude
open import Common.Equality

primitive
  primForce      : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) → (∀ x → B x) → B x
  primForceLemma : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) (f : ∀ x → B x) → primForce x f ≡ f x

force = primForce
forceLemma = primForceLemma

seq : ∀ {a b} {A : Set a} {B : Set b} → A → B → B
seq x y = force x λ _ → y

foo : (a b : Nat) → seq a b ≡ b
foo zero    _ = refl
foo (suc n) _ = refl

seqLit : (n : Nat) → seq "literal" n ≡ n
seqLit n = refl

seqType : (n : Nat) → seq Nat n ≡ n
seqType n = refl

seqPi : {A B : Set} {n : Nat} → seq (A → B) n ≡ n
seqPi = refl

seqLam : {n : Nat} → seq (λ (x : Nat) → x) n ≡ n
seqLam = refl

seqLemma : (a b : Nat) → seq a b ≡ b
seqLemma a b = forceLemma a _

evalLemma : (n : Nat) → seqLemma (suc n) n ≡ refl
evalLemma n = refl

infixr 0 _$!_
_$!_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $! x = force x f

-- Without seq, this would be exponential --

pow2 : Nat → Nat → Nat
pow2 zero    acc = acc
pow2 (suc n) acc = pow2 n $! acc + acc

lem : pow2 32 1 ≡ 4294967296
lem = refl
