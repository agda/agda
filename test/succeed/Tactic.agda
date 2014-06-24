
open import Common.Prelude
open import Common.Reflect
open import Common.Equality

postulate
  trustme : ∀ {a} {A : Set a} {x y : A} → x ≡ y

magic : Term → Term
magic _ = def (quote trustme) []

id : ∀ {a} {A : Set a} → A → A
id x = x

science : Term → Term
science _ = def (quote id) []

by-magic : ∀ n → n + 4 ≡ 3
by-magic n = tactic magic

by-science : ∀ n → 0 + n ≡ n
by-science n = tactic science | refl
