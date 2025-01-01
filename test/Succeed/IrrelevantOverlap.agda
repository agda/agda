open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

postulate
  NonZero : Nat → Set
  instance
    nonZero : ∀ {n} → NonZero (suc n)

  foo : ∀ {m n o} .{{_ : NonZero o}} → m + o ≡ n + o

bar : ∀ m o .{{_ : NonZero m}} → o + m ≡ o + m
bar m o = foo
