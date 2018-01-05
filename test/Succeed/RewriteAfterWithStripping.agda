-- 2018-01-05, Jesper: having a `rewrite` after a `with` caused problems
-- because the patterns stripped by with-desugaring were not propagated
-- to the generated rewrite-clause. This should now be fixed.

open import Agda.Builtin.Equality

postulate
  lem : Set ≡ Set

simple-test : {A : Set₁} → A ≡ Set → Set₁
simple-test {A = A} refl with Set
simple-test {A = A} refl | _ rewrite lem = A


record ⊤ : Set where constructor tt

data G : Set → Set₁ where
  d : (A : Set) → G A → G A

postulate
  exists : (A : Set) → G A
  unique : (A : Set) (x : G A) → exists A ≡ x

test : (A : Set) → G A → ⊤
test _ (d A x) with unique A x
test _ (d A _) | refl rewrite refl {x = tt} = tt
