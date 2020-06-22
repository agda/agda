{-# OPTIONS --prop --rewriting --confluence-check #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _+ℕ_)

infix 4 _≐_
data _≐_ {ℓ} {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≐ x

{-# BUILTIN REWRITE _≐_ #-}

variable
  ℓ : Level
  A B C : Set ℓ
  x y z : A

cong : (f : A → B) → x ≐ y → f x ≐ f y
cong f refl = refl

data ℤ : Set where
  zero : ℤ
  pred suc : ℤ → ℤ

postulate
  pred-suc : (x : ℤ) → pred (suc x) ≐ x
  suc-pred : (x : ℤ) → suc (pred x) ≐ x

{-# REWRITE pred-suc suc-pred #-}

_+_ : ℤ → ℤ → ℤ
zero   + y = y
pred x + y = pred (x + y)
suc x  + y = suc (x + y)

-_ : ℤ → ℤ
- zero = zero
- pred x = suc (- x)
- suc x = pred (- x)

data ℤ′ : Set where
  +[_]   : ℕ → ℤ′
  -[1+_] : ℕ → ℤ′

suc′ : ℤ′ → ℤ′
suc′ +[ x ] = +[ suc x ]
suc′ -[1+ zero ] = +[ zero ]
suc′ -[1+ suc x ] = -[1+ x ]

pred′ : ℤ′ → ℤ′
pred′ +[ zero ] = -[1+ zero ]
pred′ +[ suc x ] = +[ x ]
pred′ -[1+ x ] = -[1+ suc x ]

suc-pred′ : suc′ (pred′ x) ≐ x
suc-pred′ {+[ zero ]} = refl
suc-pred′ {+[ suc x ]} = refl
suc-pred′ { -[1+ x ]} = refl

pred-suc′ : pred′ (suc′ x) ≐ x
pred-suc′ {+[ x ]} = refl
pred-suc′ { -[1+ zero ]} = refl
pred-suc′ { -[1+ suc x ]} = refl

{-# REWRITE suc-pred′ pred-suc′ #-}

norm : ℤ → ℤ′
norm zero = +[ 0 ]
norm (pred x) = pred′ (norm x)
norm (suc x) = suc′ (norm x)

free : ℤ′ → ℤ
free +[ zero ] = zero
free +[ suc x ] = suc (free +[ x ])
free -[1+ zero ] = pred zero
free -[1+ suc x ] = pred (free -[1+ x ])
