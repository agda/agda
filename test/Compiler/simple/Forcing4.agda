module Forcing4 where

open import Common.Nat renaming (zero to Z; suc to S)
open import Lib.Fin
open import Common.Equality
open import Common.String
open import Common.IO
open import Common.Unit

Rel : (X : Set) → Set1
Rel X = X → X → Set

data _<=_ : Rel Nat where
  z<=n : ∀ n                   → Z   <= n     -- n is forced
  s<=s : ∀ m n (m<=n : m <= n) → S m <= S n   -- m and n are forced

_ℕ<_ : Rel Nat
m ℕ< n = S m <= n

fromℕ≤ : ∀ {m n} → m ℕ< n → Fin n
fromℕ≤ (s<=s .0     n      (z<=n .n)      ) = fz {n}
fromℕ≤ (s<=s .(S m) .(S n) (s<=s m n m<=n)) = fs {S n} (fromℕ≤ (s<=s m n m<=n))

fromℕ≤-toℕ : ∀ m (i : Fin m) (i<m : forget i ℕ< m) → fromℕ≤ i<m ≡ i
fromℕ≤-toℕ .(S n)     (fz {n})      (s<=s .0              .n     (z<=n .n))                = refl
fromℕ≤-toℕ .(S (S n)) (fs .{S n} y) (s<=s .(S (forget y)) .(S n) (s<=s .(forget y) n m≤n)) = cong (\ n → fs n) (fromℕ≤-toℕ (S n) y (s<=s (forget y) n m≤n))

[_/2] : Nat → Nat
[ 0       /2] = 0
[ 1       /2] = 0
[ S (S n) /2] = S [ n /2]

[1/2]-mono : (m n : Nat) → m <= n → [ m /2] <= [ n /2]
[1/2]-mono .0         .n         (z<=n n)                             = z<=n [ n /2]
[1/2]-mono .1         .(S n)     (s<=s .0     .n     (z<=n n))        = z<=n [ S n /2]
[1/2]-mono .(S (S m)) .(S (S n)) (s<=s .(S m) .(S n) (s<=s m n m<=n)) = s<=s [ m /2] [ n /2] ([1/2]-mono m n m<=n)

showEq : {X : Set}{A : X} → A ≡ A → String
showEq refl = "refl"

show<= : {m n : Nat} → m <= n → String
show<= (z<=n n)        = "0 <= " +S+ natToString n
show<= (s<=s m n m<=n) = natToString (S m) +S+ " <= " +S+ natToString (S n)

data Bot : Set where

-- Only to check that it compiles..
foo : (n : Nat) → S n <= n → Bot
foo .(S n) (s<=s .(S n) n le) = foo n le

main : IO Unit
main = putStrLn (showEq (fromℕ≤-toℕ 3 (inc (inject 1)) le)) ,,
       putStrLn (show<= ([1/2]-mono 4 6 le'))
  where
    le : 2 <= 3
    le = s<=s _ _ (s<=s _ _ (z<=n _))
    le' : 4 <= 6
    le' = s<=s _ _ (s<=s _ _ (s<=s _ _ (s<=s _ _ (z<=n _))))
