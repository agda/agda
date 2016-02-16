{-# OPTIONS --allow-unsolved-metas #-}

-- Andreas, 2014-11-25, issue found by Christopher Jenkins
-- {-# OPTIONS -v tc.with:40 #-}

open import Common.Prelude
open import Common.Equality

infixr 5 _∷_

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : {n : Nat} (x : A) (xs : Vec A n) → Vec A (suc n)

+-suc : ∀ (n m : Nat) → n + suc m ≡ suc (n + m)
+-suc zero m    = refl
+-suc (suc n) m = cong suc (+-suc n m)

swap : ∀ {A : Set} n → Vec A (n + n) → Vec A (n + n)
swap zero [] = []
swap (suc n) (x ∷ xs) with n + suc n | +-suc n n
swap (suc n) (x ∷ y ∷ xs) | .(suc (n + n)) | refl = y ∷ x ∷ swap n xs

swap-involutive : ∀ {A : Set} n → (xs : Vec A (n + n)) →
                  swap n (swap n xs) ≡ xs
swap-involutive zero [] = refl
swap-involutive {A = A} (suc n) (x ∷ xs) with swap {A = A} (suc n)
...  | f = {!!}
-- Goal before with is:
-- swap (suc n) (swap (suc n) (x ∷ xs) | n + suc n | +-suc n n) ≡ x ∷ xs

{- ERROR WAS:
A !=< ℕ of type Set
when checking that the type
{A : Set}
(n : ℕ)
(w : Vec A (suc (n + suc n)) → Vec A (suc (n + suc n)))
(x : A)
(xs : Vec A (n + suc n)) →
w (swap (suc x) (xs ∷ w) | x + suc x | +-suc x x) ≡ x ∷ xs
of the generated with function is well-formed
-}
