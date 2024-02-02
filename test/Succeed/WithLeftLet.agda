module WithLeftLet where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

infix 1 _∋_
_∋_ : (A : Set) → A → A
A ∋ x = x

f₁ : (n : Nat) → Nat
f₁ n using 2n ← n + n
         | 3n ← 2n + n
         | 4n ← 3n + n = n + 2n + 3n + 4n

_ = f₁ 1 ≡ 10 ∋ refl

f₂ : (n : Nat) → Nat
f₂ n using 2n ← n + n
         | 3n ← 2n + n
         | 4n ← 3n + n
      with 5n ← 4n + n = n + 2n + 3n + 4n + 5n

_ = f₂ 1 ≡ 15 ∋ refl

f₃ : (n : Nat) → (∀ m → m ≡ m) → Nat
f₃ n eq using 2n ← n + n rewrite eq 2n using 3n ← 2n + n = n + 2n + 3n

_ = f₃ 1 (λ _ → refl) ≡ 6 ∋ refl

data Vec (A : Set) : Nat → Set where
  [] : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

vec : {A : Set} {n : Nat} → A → Vec A n
vec {n = zero}  x = []
vec {n = suc n} x = x ∷ vec x

const : {A B : Set} → A → B → A
const x _ = x

len : ∀ {A n} → Vec A n → Nat
len {n = n} _ = n

f₄ : (n : Nat) → (Nat → Vec Nat n) → Nat
f₄ n v using 2n ← n + n with v 2n in eq
... | []                       = const 2n (2n ≡ 0 ∋ refl)
... | x ∷ xs using n′ ← len xs = const 2n (2n ≡ suc n′ + suc n′ ∋ refl)

f₅ : Nat → Nat
f₅ zero = 0
f₅ n@(suc m) using 2n ← n + n = z
  where
    z : Nat
    z with 2n + n
    ... | 3n = n + 2n + 3n

_ = f₅ 1 ≡ 6 ∋ refl
