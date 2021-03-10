open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

cong : {A B : Set} (f : A → B)
     → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

+-identityʳ : (x : Nat) → x + 0 ≡ x
+-identityʳ zero    = refl
+-identityʳ (suc n) = cong suc (+-identityʳ n)

+-assoc : (x y z : Nat) → (x + y) + z ≡ x + (y + z)
+-assoc zero    _ _ = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 x) = x1 x
inc (x1 x) = x0 (inc x)

to : Nat → Bin
to zero = (x0 nil)
to (suc x) = inc (to x)

postulate
  from : Bin → Nat

data Can : Bin → Set where
  Can- : ∀ {n} → from (to n) ≡ n → Can (to n)

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

postulate
  to'' : (x : Nat) → Σ Bin Can

to∘from' : (a : Bin) → (b : Can a) → to'' (from a) ≡ ⟨ a , b ⟩
to∘from' .(to _) (Can- x) = {!!}
