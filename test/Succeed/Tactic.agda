
open import Common.Prelude
open import Common.Reflection
open import Common.Equality
open import Common.TC

postulate
  trustme : ∀ {a} {A : Set a} {x y : A} → x ≡ y

magic : List (Arg Type) → Term → Tactic
magic _ _ = give (def (quote trustme) [])

id : ∀ {a} {A : Set a} → A → A
id x = x

science : List (Arg Type) → Term → Tactic
science _ _ = give (def (quote id) [])

by-magic : ∀ n → n + 4 ≡ 3
by-magic n = tactic magic

by-science : ∀ n → 0 + n ≡ n
by-science n = tactic science | refl
