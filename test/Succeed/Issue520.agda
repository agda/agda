-- Andreas, 2015-12-10, issue reported by Andrea Vezzosi

open import Common.Equality
open import Common.Bool

id : Bool → Bool
id true  = true
id false = false

is-id : ∀ x → x ≡ id x
is-id true  = refl
is-id false = refl

postulate
  P : Bool → Set
  b : Bool
  p : P (id b)

proof : P b
proof rewrite is-id b = p
