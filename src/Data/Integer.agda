------------------------------------------------------------------------
-- Integers
------------------------------------------------------------------------

module Data.Integer where

open import Data.Nat as ℕ
  using (ℕ) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
import Data.Nat.Show as ℕ
open import Data.Sign as Sign using (Sign) renaming (_*_ to _S*_)
open import Data.Product as Prod
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
infixl 6 _+_ _-_ _⊖_ _⊔_
infix  4 _≤_ _≤?_

------------------------------------------------------------------------
-- The types

-- Integers.

data ℤ : Set where
  -[1+_] : (n : ℕ) → ℤ  -- -[1+ n ] stands for - (1 + n).
  +_     : (n : ℕ) → ℤ  -- + n stands for n.

------------------------------------------------------------------------
-- Conversions

-- Absolute value.

∣_∣ : ℤ → ℕ
∣ + n      ∣ = n
∣ -[1+ n ] ∣ = ℕ.suc n

-- Gives the sign. For zero the sign is arbitrarily chosen to be +.

sign : ℤ → Sign
sign (+ _)    = Sign.+
sign -[1+ _ ] = Sign.-

-- Decimal string representation.

show : ℤ → String
show i = showSign (sign i) ++ ℕ.show ∣ i ∣
  where
  showSign : Sign → String
  showSign Sign.- = "-"
  showSign Sign.+ = ""

------------------------------------------------------------------------
-- A view of integers as sign + absolute value

infix 5 _◂_ _◃_

_◃_ : Sign → ℕ → ℤ
_      ◃ ℕ.zero  = + ℕ.zero
Sign.+ ◃ n       = + n
Sign.- ◃ ℕ.suc n = -[1+ n ]

◃-left-inverse : ∀ i → sign i ◃ ∣ i ∣ ≡ i
◃-left-inverse -[1+ n ]    = refl
◃-left-inverse (+ ℕ.zero)  = refl
◃-left-inverse (+ ℕ.suc n) = refl

◃-cong : ∀ {i j} → sign i ≡ sign j → ∣ i ∣ ≡ ∣ j ∣ → i ≡ j
◃-cong {i} {j} sign-≡ abs-≡ = begin
  i               ≡⟨ sym $ ◃-left-inverse i ⟩
  sign i ◃ ∣ i ∣  ≡⟨ cong₂ _◃_ sign-≡ abs-≡ ⟩
  sign j ◃ ∣ j ∣  ≡⟨ ◃-left-inverse j ⟩
  j               ∎

data SignAbs : ℤ → Set where
  _◂_ : (s : Sign) (n : ℕ) → SignAbs (s ◃ n)

signAbs : ∀ i → SignAbs i
signAbs i = PropEq.subst SignAbs (◃-left-inverse i) $
              sign i ◂ ∣ i ∣

------------------------------------------------------------------------
-- Equality is decidable

_≟_ : Decidable {ℤ} _≡_
i ≟ j with Sign._≟_ (sign i) (sign j) | ℕ._≟_ ∣ i ∣ ∣ j ∣
i ≟ j | yes sign-≡ | yes abs-≡ = yes (◃-cong sign-≡ abs-≡)
i ≟ j | no  sign-≢ | _         = no (sign-≢ ∘ cong sign)
i ≟ j | _          | no abs-≢  = no (abs-≢  ∘ cong ∣_∣)

decSetoid : DecSetoid
decSetoid = PropEq.decSetoid _≟_

------------------------------------------------------------------------
-- Arithmetic

-- Negation.

-_ : ℤ → ℤ
- (+ ℕ.suc n) = -[1+ n ]
- (+ ℕ.zero)  = + ℕ.zero
- -[1+ n ]    = + ℕ.suc n

-- Subtraction of natural numbers.

_⊖_ : ℕ → ℕ → ℤ
m       ⊖ ℕ.zero  = + m
ℕ.zero  ⊖ ℕ.suc n = -[1+ n ]
ℕ.suc m ⊖ ℕ.suc n = m ⊖ n

-- Addition.

_+_ : ℤ → ℤ → ℤ
-[1+ m ] + -[1+ n ] = -[1+ ℕ.suc (m ℕ+ n) ]
-[1+ m ] + +    n   = n ⊖ ℕ.suc m
+    m   + -[1+ n ] = m ⊖ ℕ.suc n
+    m   + +    n   = + (m ℕ+ n)

-- Subtraction.

_-_ : ℤ → ℤ → ℤ
-[1+ m ] - -[1+ n ] = n ⊖ m
-[1+ m ] - +    n   = -[1+ n ℕ+ m ]
+    m   - -[1+ n ] = + (ℕ.suc n ℕ+ m)
+    m   - +    n   = m ⊖ n

private

  -- Note that the definition i - j = - j + i evaluates differently
  -- from the definition above. For instance, the following property
  -- would require a nontrivial proof with the alternative definition:

  +-+ : ∀ m n → + m - + n ≡ m ⊖ n
  +-+ m n = refl

  -- The proof is still easy, though.

  -++ : ∀ m n → - + n + + m ≡ m ⊖ n
  -++ m ℕ.zero    = refl
  -++ m (ℕ.suc n) = refl

-- Successor.

suc : ℤ → ℤ
suc i = + 1 + i

private

  suc-is-lazy⁺ : ∀ n → suc (+ n) ≡ + ℕ.suc n
  suc-is-lazy⁺ n = refl

  suc-is-lazy⁻ : ∀ n → suc -[1+ ℕ.suc n ] ≡ -[1+ n ]
  suc-is-lazy⁻ n = refl

-- Predecessor.

pred : ℤ → ℤ
pred i = i - + 1

private

  pred-is-lazy⁺ : ∀ n → pred (+ ℕ.suc n) ≡ + n
  pred-is-lazy⁺ n = refl

  pred-is-lazy⁻ : ∀ n → pred -[1+ n ] ≡ -[1+ ℕ.suc n ]
  pred-is-lazy⁻ n = refl

-- Multiplication.

_*_ : ℤ → ℤ → ℤ
i * j = sign i S* sign j ◃ ∣ i ∣ ℕ* ∣ j ∣

-- Maximum.

_⊔_ : ℤ → ℤ → ℤ
-[1+ m ] ⊔ -[1+ n ] = -[1+ ℕ._⊓_ m n ]
-[1+ m ] ⊔ +    n   = + n
+    m   ⊔ -[1+ n ] = + m
+    m   ⊔ +    n   = + (ℕ._⊔_ m n)

-- Minimum.

_⊓_ : ℤ → ℤ → ℤ
-[1+ m ] ⊓ -[1+ n ] = -[1+ ℕ._⊔_ m n ]
-[1+ m ] ⊓ +    n   = -[1+ m ]
+    m   ⊓ -[1+ n ] = -[1+ n ]
+    m   ⊓ +    n   = + (ℕ._⊓_ m n)

------------------------------------------------------------------------
-- Ordering

data _≤_ : ℤ → ℤ → Set where
  -≤+ : ∀ {m n} → -[1+ m ] ≤ + n
  -≤- : ∀ {m n} → (n≤m : ℕ._≤_ n m) → -[1+ m ] ≤ -[1+ n ]
  +≤+ : ∀ {m n} → (m≤n : ℕ._≤_ m n) → + m ≤ + n

drop‿+≤+ : ∀ {m n} → + m ≤ + n → ℕ._≤_ m n
drop‿+≤+ (+≤+ m≤n) = m≤n

drop‿-≤- : ∀ {m n} → -[1+ m ] ≤ -[1+ n ] → ℕ._≤_ n m
drop‿-≤- (-≤- n≤m) = n≤m

_≤?_ : Decidable _≤_
-[1+ m ] ≤? -[1+ n ] = Dec.map (-≤- , drop‿-≤-) (ℕ._≤?_ n m)
-[1+ m ] ≤? +    n   = yes -≤+
+    m   ≤? -[1+ n ] = no λ ()
+    m   ≤? +    n   = Dec.map (+≤+ , drop‿+≤+) (ℕ._≤?_ m n)

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
                  ; reflexive     = refl′
                  ; trans         = trans
                  ; ∼-resp-≈      = PropEq.resp₂ _≤_
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
  module ℕO = DecTotalOrder ℕ.decTotalOrder

  refl′ : _≡_ ⇒ _≤_
  refl′ { -[1+ n ]} refl = -≤- ℕO.refl
  refl′ {+ n}       refl = +≤+ ℕO.refl

  trans : Transitive _≤_
  trans -≤+       (+≤+ n≤m) = -≤+
  trans (-≤- n≤m) -≤+       = -≤+
  trans (-≤- n≤m) (-≤- k≤n) = -≤- (ℕO.trans k≤n n≤m)
  trans (+≤+ m≤n) (+≤+ n≤k) = +≤+ (ℕO.trans m≤n n≤k)

  antisym : Antisymmetric _≡_ _≤_
  antisym -≤+       ()
  antisym (-≤- n≤m) (-≤- m≤n) = cong -[1+_] $ ℕO.antisym m≤n n≤m
  antisym (+≤+ m≤n) (+≤+ n≤m) = cong +_     $ ℕO.antisym m≤n n≤m

  total : Total _≤_
  total (-[1+ m ]) (-[1+ n ]) = [ inj₂ ∘′ -≤- , inj₁ ∘′ -≤- ]′ $ ℕO.total m n
  total (-[1+ m ]) (+    n  ) = inj₁ -≤+
  total (+    m  ) (-[1+ n ]) = inj₂ -≤+
  total (+    m  ) (+    n  ) = [ inj₁ ∘′ +≤+ , inj₂ ∘′ +≤+ ]′ $ ℕO.total m n

poset : Poset
poset = DecTotalOrder.poset decTotalOrder

import Relation.Binary.PartialOrderReasoning as POR
module ≤-Reasoning = POR poset
  renaming (_≈⟨_⟩_ to _≡⟨_⟩_)
