-- Andrea & Andreas, 2014-11-12
-- Pruning projected vars during solving

open import Common.Product
open import Common.Equality

postulate
  A : Set

works1 : {q1 : Set} {q2 : Set → Set} ->
       let M : Set -> Set; M = _ in {z : Set} -> q1 ≡ M (q2 z)
works1 = refl

works2 : {q1 : Set} {q2 : Set → Set} ->
       let M : Set -> Set; M = _ in q1 ≡ M (q2 A)
works2 = refl

works3 : {q : Set × Set} ->
       let M : Set -> Set; M = _ in proj₁ q ≡ M (proj₂ q)
works3 = refl

test1 : {q : Set × (Set → Set)} ->
       let M : Set -> Set; M = _ in {z : Set} -> proj₁ q ≡ M (proj₂ q z)
test1 = refl

test2 : {q : Set × (Set → Set)} ->
       let M : Set -> Set; M = _ in proj₁ q ≡ M (proj₂ q A)
test2 = refl

-- these tests should succeed, as expanding q into a pair gets us back to
-- works1 and works2
