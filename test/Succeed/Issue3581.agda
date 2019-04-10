-- Andreas, 2018-04-10, issue #3581, reported by 3abc, test case by Andrea

-- Regression in the termination checker introduced together
-- with collecting function calls also in the type signatures
-- (fix of #1556).

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

I = Bool
i0 = true
i1 = false

record PathP {l} (A : I → Set l) (x : A i0) (y : A i1) : Set l where
  field
    apply : ∀ i → A i

open PathP

_[_≡_] = PathP

_≡_ : ∀ {l} {A : Set l} → A → A → Set l
_≡_ {A = A} = PathP (\ _ → A)

refl : ∀ {l} {A : Set l} {x : A} → x ≡ x
refl {x = x} .apply _ = x

cong' : ∀ {l ℓ'} {A : Set l}{B : A → Set ℓ'} (f : (a : A) → B a) {x y} (p : x ≡ y)
     → PathP (λ i → B (p .apply i)) (f (p .apply i0)) (f (p .apply i1))
cong' f p .apply = λ i → f (p .apply i)

foo : Nat → Nat
foo zero = zero
foo (suc n) = Z .apply true .apply true
 where
 postulate
   Z : (\ _ → foo n ≡ foo n) [ (cong' foo (refl {x = n})) ≡ (\ { .apply i → cong' foo (refl {x = n}) .apply i }) ]
