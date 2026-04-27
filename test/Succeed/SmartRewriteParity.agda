{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

variable
  A B C : Set _
  x y z : A

infix 4 _≡[_]≡_

sym : x ≡ y → y ≡ x
sym refl = refl

_∙_ : x ≡ y → y ≡ z → x ≡ z
refl ∙ p = p

ap : (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

_≡[_]≡_ : A → A ≡ B → B → Set _
x ≡[ refl ]≡ y = x ≡ y

data Parity : Set where
  odd  : Parity
  even : Parity

variable
  p q : Parity

inv : Parity → Parity
inv odd  = even
inv even = odd

_xor_ : Parity → Parity → Parity
even xor q = q
odd  xor q = inv q

inv-inv : inv (inv p) ≡ p
inv-inv {p = even} = refl
inv-inv {p = odd}  = refl

inv-xor : inv p xor q ≡ inv (p xor q)
inv-xor {p = even} = refl
inv-xor {p = odd}  = sym inv-inv

xor-even : p xor even ≡ p
xor-even {p = even} = refl
xor-even {p = odd}  = refl

data Nat : Parity → Set where
  ze : Nat even
  su : Nat (inv p) → Nat p

variable
  n m : Nat _

_+_ : Nat p → Nat q → Nat (p xor q)
ze   + m = m
_+_ {p = p} {q = q} (su n) m
  rewrite inv-xor {p} {q}
  = su (n + m)

+ze : n + ze ≡[ ap Nat xor-even ]≡ n
+ze {n = ze}   = refl
+ze {n = su {p = p} n}
  rewrite xor-even {p}
  rewrite inv-xor {p} {even}
  with refl ← xor-even {inv p}
  rewrite +ze {n = n}
  = refl

xor-even-inv : xor-even {inv p} ≡ inv-xor {p} {even} ∙ ap inv (xor-even {p})
xor-even-inv {p = odd}  = refl
xor-even-inv {p = even} = refl

-- '--without-K' version
+ze' : n + ze ≡[ ap Nat xor-even ]≡ n
+ze' {n = ze}   = refl
+ze' {n = su {p = p} n}
  rewrite xor-even {p}
  rewrite inv-xor {p} {even}
  rewrite xor-even-inv {p}
  rewrite +ze' {n = n}
  = refl
