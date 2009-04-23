------------------------------------------------------------------------
-- Integers
------------------------------------------------------------------------

module Data.Integer where

open import Data.Nat as N using (ℕ)
import Data.Nat.Show as N
open import Data.Sign as Sign using (Sign)
open import Data.Product
open import Data.String using (String; _++_)
open import Data.Function
open import Data.Sum as Sum
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; cong; cong₂)
open PropEq.≡-Reasoning

infix  8 +_ -_
infixl 7 _*_ _⊓_
infixl 6 _+_ _-_ _⊔_
infix  4 _≤_ _≤?_

infix  8 :+_ :-_
infixl 7 _*'_
infixl 6 _+'_ _-'_

------------------------------------------------------------------------
-- The types

-- Integers.

data ℤ : Set where
  :-_ : (n : ℕ) → ℤ  -- :- n stands for - (n + 1).
  :0  : ℤ            -- :0 stands for 0.
  :+_ : (n : ℕ) → ℤ  -- :+ n stands for   (n + 1).

-- A non-canonical representation of integers.

ℤ' : Set
ℤ' = Sign × ℕ

------------------------------------------------------------------------
-- Conversions

-- From natural numbers.

+_ : ℕ → ℤ
+ N.zero  = :0
+ N.suc n = :+ n

-- Negation.

-_ : ℤ → ℤ
- :- n = :+ n
- :0   = :0
- :+ n = :- n

-- Conversion from sign + absolute value.

ℤ'toℤ : ℤ' → ℤ
ℤ'toℤ (Sign.:- , n) = - + n
ℤ'toℤ (Sign.:0 , _) = :0
ℤ'toℤ (Sign.:+ , n) = + n

-- Absolute value.

∣_∣ : ℤ → ℕ
∣ :+ n ∣ = N.suc n
∣ :0   ∣ = N.zero
∣ :- n ∣ = N.suc n

-- Gives the sign.

sign : ℤ → Sign
sign (:- _) = Sign.:-
sign :0     = Sign.:0
sign (:+ _) = Sign.:+

-- Conversion to sign + absolute value.

ℤtoℤ' : ℤ → ℤ'
ℤtoℤ' i = (sign i , ∣ i ∣)

-- Decimal string representation.

show : ℤ → String
show i = showSign (sign i) ++ N.show ∣ i ∣
  where
  showSign : Sign → String
  showSign Sign.:- = "-"
  showSign _       = ""

------------------------------------------------------------------------
-- Arithmetic

-- Negation is defined above.

suc : ℤ → ℤ
suc (:- N.suc n) = :- n
suc (:- N.zero)  = :0
suc :0           = :+ 0
suc (:+ n)       = :+ N.suc n

private module G = N.GeneralisedArithmetic :0 suc

pred : ℤ → ℤ
pred (:- n)       = :- N.suc n
pred :0           = :- 0
pred (:+ N.zero)  = :0
pred (:+ N.suc n) = :+ n

private
  _+'_ : ℕ → ℤ → ℤ
  _+'_ = G.add

  _-'_ : ℕ → ℤ → ℤ
  n       -' :0         = + n
  N.zero  -' i          = - i
  N.suc n -' :+ N.zero  = + n
  N.suc n -' :+ N.suc m = n -' :+ m
  n       -' :- i       = n +' :+ i

_+_ : ℤ → ℤ → ℤ
:- n + i = - (N.suc n -' i)
:0   + i = i
:+ n + i = N.suc n +' i

_-_ : ℤ → ℤ → ℤ
:- n - i = - (N.suc n +' i)
:0   - i = - i
:+ n - i = N.suc n -' i

private
  _*'_ : ℕ → ℤ → ℤ
  _*'_ = G.mul _+_

_*_ : ℤ → ℤ → ℤ
:- n * i = - (N.suc n *' i)
:0   * i = :0
:+ n * i = N.suc n *' i

_⊔_ : ℤ → ℤ → ℤ
:- m ⊔ :- n = :- (N._⊓_ m n)
:- _ ⊔ :0   = :0
:- _ ⊔ :+ n = :+ n
:0   ⊔ :- _ = :0
:0   ⊔ :0   = :0
:0   ⊔ :+ n = :+ n
:+ m ⊔ :- _ = :+ m
:+ m ⊔ :0   = :+ m
:+ m ⊔ :+ n = :+ (N._⊔_ m n)

_⊓_ : ℤ → ℤ → ℤ
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

ℤ'toℤ-left-inverse : ∀ i → ℤ'toℤ (ℤtoℤ' i) ≡ i
ℤ'toℤ-left-inverse (:- n) = refl
ℤ'toℤ-left-inverse :0     = refl
ℤ'toℤ-left-inverse (:+ n) = refl

drop-ℤtoℤ' : ∀ {i j} → ℤtoℤ' i ≡ ℤtoℤ' j → i ≡ j
drop-ℤtoℤ' {i} {j} eq = begin
  i
    ≡⟨ sym (ℤ'toℤ-left-inverse i) ⟩
  ℤ'toℤ (ℤtoℤ' i)
    ≡⟨ cong ℤ'toℤ eq ⟩
  ℤ'toℤ (ℤtoℤ' j)
    ≡⟨ ℤ'toℤ-left-inverse j ⟩
  j
    ∎

_≟_ : Decidable {ℤ} _≡_
i ≟ j with Sign._≟_ (sign i) (sign j) | N._≟_ ∣ i ∣ ∣ j ∣
i ≟ j | yes sign-≡ | yes abs-≡ = yes (drop-ℤtoℤ' eq)
                                   where eq = cong₂ (_,_) sign-≡ abs-≡
i ≟ j | no  sign-≢ | _         = no (sign-≢ ∘ cong sign)
i ≟ j | _          | no abs-≢  = no (abs-≢  ∘ cong ∣_∣)

decSetoid : DecSetoid
decSetoid = PropEq.decSetoid _≟_

------------------------------------------------------------------------
-- Ordering

data _≤_ : ℤ → ℤ → Set where
  0≤0   :           :0   ≤ :0
  0≤n   : ∀ {x}   → :0   ≤ :+ x
  -n≤0  : ∀ {n}   → :- n ≤ :0
  -n≤+m : ∀ {n m} → :- n ≤ :+ m
  -n≤-m : ∀ {n m} → (m≤n : N._≤_ m n) → :- n ≤ :- m
  +n≤+m : ∀ {n m} → (n≤m : N._≤_ n m) → :+ n ≤ :+ m

+≤-elim : ∀ {n m} → :+ n ≤ :+ m → N._≤_ n m
+≤-elim (+n≤+m n≤m) = n≤m

-≤-elim : ∀ {n m} → :- m ≤ :- n → N._≤_ n m
-≤-elim (-n≤-m m≤n) = m≤n

_≤?_ : Decidable _≤_
(:- n) ≤? :0      = yes -n≤0
(:- n) ≤? (:+ n') = yes -n≤+m
:0     ≤? (:- n)  = no λ()
:0     ≤? :0      = yes 0≤0
:0     ≤? (:+ n)  = yes 0≤n
(:+ n) ≤? (:- n') = no λ()
(:+ n) ≤? :0      = no λ()
(:+ n) ≤? (:+ m)  = Dec.map (+n≤+m , +≤-elim) (N._≤?_ n m)
(:- n) ≤? (:- m)  = Dec.map (-n≤-m , -≤-elim) (N._≤?_ m n)

decTotalOrder : DecTotalOrder
decTotalOrder = record
  { carrier         = ℤ
  ; _≈_             = _≡_
  ; _≤_             = _≤_
  ; isDecTotalOrder = record
      { isTotalOrder = record
          { isPartialOrder = record
              { isPreorder = record
                  { isEquivalence = PropEq.isEquivalence
                  ; reflexive     = refl'
                  ; trans         = trans
                  ; ≈-resp-∼      = PropEq.resp _≤_
                  }
                ; antisym  = antisym
              }
          ; total          = total
          }
      ; _≟_          = _≟_
      ; _≤?_         = _≤?_
      }
  }
  where
  refl' : _≡_ ⇒ _≤_
  refl' {:- N.zero}  refl = -n≤-m N.z≤n
  refl' {:- N.suc n} refl = -n≤-m (N.s≤s (-≤-elim (refl' refl)))
  refl' {:0}         refl = 0≤0
  refl' {:+ 0}       refl = +n≤+m N.z≤n
  refl' {:+ N.suc n} refl = +n≤+m (N.s≤s (+≤-elim (refl' refl)))

  trans : Transitive _≤_
  trans 0≤0         0≤0         = 0≤0
  trans 0≤0         0≤n         = 0≤n
  trans 0≤n         (+n≤+m n≤m) = 0≤n
  trans -n≤0        0≤0         = -n≤0
  trans -n≤0        0≤n         = -n≤+m
  trans -n≤+m       (+n≤+m n≤m) = -n≤+m
  trans (-n≤-m n≤m) -n≤0        = -n≤0
  trans (-n≤-m n≤m) -n≤+m       = -n≤+m
  trans (-n≤-m m≤n) (-n≤-m k≤m) = -n≤-m (DecTotalOrder.trans N.decTotalOrder k≤m m≤n)
  trans (+n≤+m n≤m) (+n≤+m m≤k) = +n≤+m (DecTotalOrder.trans N.decTotalOrder n≤m m≤k)

  antisym : Antisymmetric _≡_ _≤_
  antisym 0≤0         0≤0          = refl
  antisym (-n≤-m m≤n) (-n≤-m n≤m)  with DecTotalOrder.antisym N.decTotalOrder m≤n n≤m
  ... | refl = refl
  antisym (+n≤+m n≤m) (+n≤+m n≤m') with DecTotalOrder.antisym N.decTotalOrder n≤m n≤m'
  ... | refl = refl
  antisym 0≤n   ()
  antisym -n≤0  ()
  antisym -n≤+m ()

  total : Total _≤_
  total (:- n) (:- m) with DecTotalOrder.total N.decTotalOrder n m
  ... | inj₁ n≤m = inj₂ (-n≤-m n≤m)
  ... | inj₂ m≤n = inj₁ (-n≤-m m≤n)
  total (:- n) :0      = inj₁ -n≤0
  total (:- n) (:+ n') = inj₁ -n≤+m
  total :0     (:- n)  = inj₂ -n≤0
  total :0     :0      = inj₁ 0≤0
  total :0     (:+ n)  = inj₁ 0≤n
  total (:+ n) (:- n') = inj₂ -n≤+m
  total (:+ n) :0      = inj₂ 0≤n
  total (:+ n) (:+ m)  =
    Sum.map +n≤+m +n≤+m (DecTotalOrder.total N.decTotalOrder n m)

poset : Poset
poset = DecTotalOrder.poset decTotalOrder

import Relation.Binary.PartialOrderReasoning as POR
module ≤-Reasoning = POR poset
  renaming (_≈⟨_⟩_ to _≡⟨_⟩_)
