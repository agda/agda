------------------------------------------------------------------------
-- Integers
------------------------------------------------------------------------

module Data.Integer where

import Data.Nat as N
open N using (ℕ)
import Data.Nat.Show as N
import Data.Sign as Sign
open Sign using (Sign)
open import Data.Product
open import Data.String using (String; _++_)
open import Data.Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

infix  8 +_ -_
infixl 7 _*_ _⊓_
infixl 6 _+_ _-_ _⊔_

infix  8 :+_ :-_
infixl 7 _*'_
infixl 6 _+'_ _-'_

------------------------------------------------------------------------
-- The types

-- Integers.

data ℤ : Set where
  :-_ : (n : ℕ) -> ℤ  -- :- n stands for - (n + 1).
  :0  : ℤ             -- :0 stands for 0.
  :+_ : (n : ℕ) -> ℤ  -- :+ n stands for   (n + 1).

-- A non-canonical representation of integers.

ℤ' : Set
ℤ' = Sign × ℕ

------------------------------------------------------------------------
-- Conversions

-- From natural numbers.

+_ : ℕ -> ℤ
+ N.zero  = :0
+ N.suc n = :+ n

-- Negation.

-_ : ℤ -> ℤ
- :- n = :+ n
- :0   = :0
- :+ n = :- n

-- Conversion from sign + absolute value.

ℤ'toℤ : ℤ' -> ℤ
ℤ'toℤ (Sign.:- , n) = - + n
ℤ'toℤ (Sign.:0 , _) = :0
ℤ'toℤ (Sign.:+ , n) = + n

-- Absolute value.

∣_∣ : ℤ -> ℕ
∣ :+ n ∣ = N.suc n
∣ :0   ∣ = N.zero
∣ :- n ∣ = N.suc n

-- Gives the sign.

sign : ℤ -> Sign
sign (:- _) = Sign.:-
sign :0     = Sign.:0
sign (:+ _) = Sign.:+

-- Conversion to sign + absolute value.

ℤtoℤ' : ℤ -> ℤ'
ℤtoℤ' i = (sign i , ∣ i ∣)

-- Decimal string representation.

show : ℤ -> String
show i = showSign (sign i) ++ N.show ∣ i ∣
  where
  showSign : Sign -> String
  showSign Sign.:- = "-"
  showSign _       = ""

------------------------------------------------------------------------
-- Arithmetic

-- Negation is defined above.

suc : ℤ -> ℤ
suc (:- N.suc n) = :- n
suc (:- N.zero)  = :0
suc :0           = :+ 0
suc (:+ n)       = :+ N.suc n

private module G = N.GeneralisedArithmetic :0 suc

pred : ℤ -> ℤ
pred (:- n)       = :- N.suc n
pred :0           = :- 0
pred (:+ N.zero)  = :0
pred (:+ N.suc n) = :+ n

private
  _+'_ : ℕ -> ℤ -> ℤ
  _+'_ = G.add

  _-'_ : ℕ -> ℤ -> ℤ
  n       -' :0         = + n
  N.zero  -' i          = - i
  N.suc n -' :+ N.zero  = + n
  N.suc n -' :+ N.suc m = n -' :+ m
  n       -' :- i       = n +' :+ i

_+_ : ℤ -> ℤ -> ℤ
:- n + i = - (N.suc n -' i)
:0   + i = i
:+ n + i = N.suc n +' i

_-_ : ℤ -> ℤ -> ℤ
:- n - i = - (N.suc n +' i)
:0   - i = - i
:+ n - i = N.suc n -' i

private
  _*'_ : ℕ -> ℤ -> ℤ
  _*'_ = G.mul _+_

_*_ : ℤ -> ℤ -> ℤ
:- n * i = - (N.suc n *' i)
:0   * i = :0
:+ n * i = N.suc n *' i

_⊔_ : ℤ -> ℤ -> ℤ
:- m ⊔ :- n = :- (N._⊓_ m n)
:- _ ⊔ :0   = :0
:- _ ⊔ :+ n = :+ n
:0   ⊔ :- _ = :0
:0   ⊔ :0   = :0
:0   ⊔ :+ n = :+ n
:+ m ⊔ :- _ = :+ m
:+ m ⊔ :0   = :+ m
:+ m ⊔ :+ n = :+ (N._⊔_ m n)

_⊓_ : ℤ -> ℤ -> ℤ
:- m ⊓ :- n = :- (N._⊔_ m n)
:- m ⊓ :0   = :- m
:- m ⊓ :+ _ = :- m
:0   ⊓ :- n = :- n
:0   ⊓ :0   = :0
:0   ⊓ :+ _ = :0
:+ _ ⊓ :- n = :- n
:+ _ ⊓ :0   = :0
:+ m ⊓ :+ n = :+ (N._⊓_ m n)

------------------------------------------------------------------------
-- Equality

ℤ'toℤ-left-inverse : forall i -> ℤ'toℤ (ℤtoℤ' i) ≡ i
ℤ'toℤ-left-inverse (:- n) = ≡-refl
ℤ'toℤ-left-inverse :0     = ≡-refl
ℤ'toℤ-left-inverse (:+ n) = ≡-refl

drop-ℤtoℤ' : forall {i j} -> ℤtoℤ' i ≡ ℤtoℤ' j -> i ≡ j
drop-ℤtoℤ' {i} {j} eq = begin
  i
    ≡⟨ ≡-sym (ℤ'toℤ-left-inverse i) ⟩
  ℤ'toℤ (ℤtoℤ' i)
    ≡⟨ ≡-cong ℤ'toℤ eq ⟩
  ℤ'toℤ (ℤtoℤ' j)
    ≡⟨ ℤ'toℤ-left-inverse j ⟩
  j
    ∎

_≟_ : Decidable {ℤ} _≡_
i ≟ j with Sign._≟_ (sign i) (sign j) | N._≟_ ∣ i ∣ ∣ j ∣
i ≟ j | yes sign-≡ | yes abs-≡ = yes (drop-ℤtoℤ' eq)
                                   where eq = ≡-cong₂ (_,_) sign-≡ abs-≡
i ≟ j | no  sign-≢ | _         = no (sign-≢ ∘ ≡-cong sign)
i ≟ j | _          | no abs-≢  = no (abs-≢  ∘ ≡-cong ∣_∣)

decSetoid : DecSetoid
decSetoid = ≡-decSetoid _≟_
