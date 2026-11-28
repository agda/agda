-- Jozef, 2026-11-27, issue #7975
-- The type of the with-function below contains a chain of n function types
-- and two chains of n lambdas.  Checking it took time quadratic in n.

-- With --double-check, the conversion checker compares these chains,
-- which still takes time quadratic in n.
{-# OPTIONS --no-double-check #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

T : (n : Nat) (A B : Set) → Set
T zero    A B = B
T (suc n) A B = A → T n A B

t : {A B : Set} (n : Nat) (b : B) → T n A B
t zero    b = b
t (suc n) b = λ _ → t n b

n = 2000

k : {B : Set} (b : B) → T n Nat B
k b = t n b

thm : {A B : Set} (a b : B) (eq : a ≡ b) → k a ≡ k b
thm a b eq rewrite eq = refl
