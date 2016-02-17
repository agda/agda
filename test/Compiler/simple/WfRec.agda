
module _ where

open import Common.Prelude renaming (_∸_ to _-_) -- work-around for #1855

data Acc {a} {A : Set a} (_<_ : A → A → Set) (x : A) : Set a where
  acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x

data _<_ : Nat → Nat → Set where
  zero : ∀ {n} → zero < suc n
  suc  : ∀ {n m} → n < m → suc n < suc m

_≤_ : Nat → Nat → Set
n ≤ m = n < suc m

data LeqView (n : Nat) : Nat → Set where
  less : ∀ {m} → n < m → LeqView n m
  equal : LeqView n n

leqView : ∀ {n m} → n ≤ m → LeqView n m
leqView {m = zero} zero = equal
leqView {m = suc m} zero = less zero
leqView {m = zero} (suc ())
leqView {m = suc m} (suc leq) with leqView leq
leqView {._} {suc m} (suc leq) | less lt = less (suc lt)
leqView {.(suc m)} {suc m} (suc lt) | equal = equal

case_of_ : ∀ {A B : Set} → A → (A → B) → B
case x of f = f x

wfAux : ∀ {n y} → (∀ z → z < n → Acc _<_ z) → y ≤ n → Acc _<_ y
wfAux f leq with leqView leq
wfAux f leq | less lt = f _ lt
wfAux f leq | equal = acc f

wfNat : ∀ n → Acc _<_ n
wfNat zero = acc λ _ ()
wfNat (suc n) with wfNat n
... | acc f = acc (λ y lt → wfAux f lt)

≤-refl : ∀ n → n ≤ n
≤-refl zero = zero
≤-refl (suc n) = suc (≤-refl n)

wk< : ∀ {n m} → n < m → n < suc m
wk< zero = zero
wk< (suc lt) = suc (wk< lt)

less-minus : ∀ n m → (suc n - suc m) ≤ n
less-minus n zero    = ≤-refl n
less-minus zero (suc m) = zero
less-minus (suc n) (suc m) = wk< (less-minus n m)

NonZero : Nat → Set
NonZero zero = ⊥
NonZero (suc _) = ⊤

divsuc : ∀ n → Nat → Acc _<_ n → Nat
divsuc 0 _ _ = 0
divsuc (suc n) m (acc f) =
  suc (divsuc (n - m) m (f _ (less-minus n m)))

div : Nat → (m : Nat) → {_ : NonZero m} → Nat
div n zero {}
div n (suc m) = divsuc n m (wfNat n)

main : IO Unit
main = printNat (div 1000000 1000)
