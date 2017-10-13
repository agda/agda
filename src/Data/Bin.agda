------------------------------------------------------------------------
-- The Agda standard library
--
-- A binary representation of natural numbers
------------------------------------------------------------------------

module Data.Bin where

open import Data.Nat as Nat
  using (ℕ; zero; z≤n; s≤s) renaming (suc to 1+_)
open import Data.Digit  using (fromDigits; toDigits; Bit)
open import Data.Fin as Fin using (Fin; zero)
  renaming (suc to 1+_)
open import Data.Fin.Properties as FP using (_+′_)
open import Data.List.Base as List hiding (downFrom)
open import Function
open import Data.Product using (uncurry; _,_; _×_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym)
open import Relation.Binary.List.StrictLex
open import Relation.Nullary
open import Relation.Nullary.Decidable

------------------------------------------------------------------------
-- Bits

pattern 0b = zero
pattern 1b = 1+ zero
pattern ⊥b = 1+ 1+ ()

------------------------------------------------------------------------
-- The type

-- A representation of binary natural numbers in which there is
-- exactly one representative for every number. The function toℕ below
-- defines the meaning of Bin.

-- `bs 1#` stands for the binary number "1<reverse bs>" e.g.
-- `(0b ∷ [])           1#` represents "10"
-- `(0b ∷ 1b ∷ 1b ∷ []) 1#` represents "1110"

Bin⁺ : Set
Bin⁺ = List Bit

infix 8 _1#

data Bin : Set where
  0#  : Bin
  _1# : (bs : Bin⁺) → Bin

------------------------------------------------------------------------
-- Conversion functions

-- Converting to a list of bits starting with the _least_ significant
-- one.

toBits : Bin → List Bit
toBits 0#      = [ 0b ]
toBits (bs 1#) = bs ++ [ 1b ]

-- Converting to a natural number.

toℕ : Bin → ℕ
toℕ = fromDigits ∘ toBits

-- Converting from a list of bits, starting with the _least_
-- significant one.

fromBits : List Bit → Bin
fromBits []        = 0#
fromBits (b  ∷ bs) with fromBits bs
fromBits (b  ∷ bs) | bs′ 1# = (b ∷ bs′) 1#
fromBits (0b ∷ bs) | 0#     = 0#
fromBits (1b ∷ bs) | 0#     = [] 1#
fromBits (⊥b ∷ bs) | _

private
  pattern 2+_ n = 1+ 1+ n

  ntoBits′ : ℕ → ℕ → List Bit
  ntoBits′     0      _  = []
  ntoBits′     1      0  = 0b ∷ 1b ∷ []
  ntoBits′     1      1  = 1b ∷ []
  ntoBits′ (2+ k)     0  = 0b ∷ ntoBits′ (1+ k) k
  ntoBits′ (2+ k)     1  = 1b ∷ ntoBits′ (1+ k) (1+ k)
  ntoBits′ (1+ k) (2+ n) = ntoBits′ k n

  ntoBits : ℕ → List Bit
  ntoBits n = ntoBits′ n n

-- Converting from a natural number.

fromℕ : ℕ → Bin
fromℕ n = fromBits $ ntoBits n

------------------------------------------------------------------------
-- Order relation.

-- Wrapped so that the parameters can be inferred.

infix 4 _<_

data _<_ (b₁ b₂ : Bin) : Set where
  less : (lt : (Nat._<_ on toℕ) b₁ b₂) → b₁ < b₂

less-injective : ∀ {b₁ b₂} {lt₁ lt₂} → (b₁ < b₂ ∋ less lt₁) ≡ less lt₂ → lt₁ ≡ lt₂
less-injective refl = refl

------------------------------------------------------------------------
-- Arithmetic

-- Power of two.

infixr 8 2^_

2^_ : ℕ → Bin⁺
2^ 0      = []
2^ (1+ n) = 0b ∷ 2^ n

-- Base 2 logarithm (rounded downwards).

⌊log₂_⌋ : Bin⁺ → ℕ
⌊log₂ (b ∷ bs) ⌋ = 1+ ⌊log₂ bs ⌋
⌊log₂ []       ⌋ = 0

-- Multiplication by 2.

infix 7 _*2 _*2+1

_*2 : Bin → Bin
0#      *2 = 0#
(bs 1#) *2 = (0b ∷ bs) 1#

_*2+1 : Bin → Bin
0#      *2+1 = [] 1#
(bs 1#) *2+1 = (1b ∷ bs) 1#

-- Division by 2, rounded downwards.

⌊_/2⌋ : Bin → Bin
⌊ 0#          /2⌋ = 0#
⌊ [] 1#       /2⌋ = 0#
⌊ (b ∷ bs) 1# /2⌋ = bs 1#

-- Addition.

Carry : Set
Carry = Bit

addBits : Carry → Bit → Bit → Carry × Bit
addBits c b₁ b₂ with c +′ (b₁ +′ b₂)
... | zero           = (0b , 0b)
... | 1+ zero        = (0b , 1b)
... | 1+ 1+ zero     = (1b , 0b)
... | 1+ 1+ 1+ zero  = (1b , 1b)
... | 1+ 1+ 1+ 1+ ()

addCarryToBitList : Carry → List Bit → List Bit
addCarryToBitList 0b bs        = bs
addCarryToBitList 1b []        = 1b ∷ []
addCarryToBitList 1b (0b ∷ bs) = 1b ∷ bs
addCarryToBitList 1b (1b ∷ bs) = 0b ∷ addCarryToBitList 1b bs
addCarryToBitList ⊥b _
addCarryToBitList _  (⊥b ∷ _)

addBitLists : Carry → List Bit → List Bit → List Bit
addBitLists c []         bs₂        = addCarryToBitList c bs₂
addBitLists c bs₁        []         = addCarryToBitList c bs₁
addBitLists c (b₁ ∷ bs₁) (b₂ ∷ bs₂) with addBits c b₁ b₂
... | (c' , b') = b' ∷ addBitLists c' bs₁ bs₂

infixl 6 _+_

_+_ : Bin → Bin → Bin
m + n = fromBits (addBitLists 0b (toBits m) (toBits n))

-- Multiplication.

infixl 7 _*_

_*_ : Bin → Bin → Bin
0#                  * n = 0#
[]               1# * n = n
-- (b + 2 * bs 1#) * n = b * n + 2 * (bs 1# * n)
(b  ∷ bs) 1# * n with bs 1# * n
(b  ∷ bs) 1# * n | 0#     = 0#
(0b ∷ bs) 1# * n | bs' 1# = (0b ∷ bs') 1#
(1b ∷ bs) 1# * n | bs' 1# = n + (0b ∷ bs') 1#
(⊥b ∷ _)  1# * _ | _

-- Successor.

suc : Bin → Bin
suc n = [] 1# + n

-- Division by 2, rounded upwards.

⌈_/2⌉ : Bin → Bin
⌈ n /2⌉ = ⌊ suc n /2⌋

-- Predecessor.

pred : Bin⁺ → Bin
pred []        = 0#
pred (0b ∷ bs) = pred bs *2+1
pred (1b ∷ bs) = (zero ∷ bs) 1#
pred (⊥b ∷ bs)

-- downFrom n enumerates all numbers from n - 1 to 0. This function is
-- linear in n. Analysis: fromℕ takes linear time, and the preds used
-- take amortised constant time (to see this, let the cost of a pred
-- be 2, and put 1 debit on every bit which is 1).

downFrom : ℕ → List Bin
downFrom n = helper n (fromℕ n)
  where
  helper : ℕ → Bin → List Bin
  helper zero   0#      = []
  helper (1+ n) (bs 1#) = n′ ∷ helper n n′
    where n′ = pred bs
  -- Impossible cases:
  helper zero   (_ 1#)  = []
  helper (1+ _) 0#      = []

------------------------------------------------------------------------
-- Tests

-- The tests below are run when this module is type checked.

-- First some test helpers:

private

  testLimit : ℕ
  testLimit = 5

  nats : List ℕ
  nats = List.downFrom testLimit

  nats⁺ : List ℕ
  nats⁺ = filter (λ n → ⌊ 1 Nat.≤? n ⌋) nats

  natPairs : List (ℕ × ℕ)
  natPairs = List.zip nats (reverse nats)

  _=[_]_ : (ℕ → ℕ) → List ℕ → (Bin → Bin) → Set
  f =[ ns ] g = List.map f ns ≡ List.map (toℕ ∘ g ∘ fromℕ) ns

  _=[_]₂_ : (ℕ → ℕ → ℕ) → List (ℕ × ℕ) → (Bin → Bin → Bin) → Set
  f =[ ps ]₂ g =
    List.map (uncurry f) ps ≡ List.map (toℕ ∘ uncurry (g on fromℕ)) ps

-- And then the tests:

private

  test-*2+1 : (λ n → Nat._+_ (Nat._*_ n 2) 1) =[ nats ] _*2+1
  test-*2+1 = refl

  test-*2 : (λ n → Nat._*_ n 2) =[ nats ] _*2
  test-*2 = refl

  test-⌊_/2⌋ : Nat.⌊_/2⌋ =[ nats ] ⌊_/2⌋
  test-⌊_/2⌋ = refl

  test-+ : Nat._+_ =[ natPairs ]₂ _+_
  test-+ = refl

  test-* : Nat._*_ =[ natPairs ]₂ _*_
  test-* = refl

  test-suc : 1+_ =[ nats ] suc
  test-suc = refl

  test-⌈_/2⌉ : Nat.⌈_/2⌉ =[ nats ] ⌈_/2⌉
  test-⌈_/2⌉ = refl

  drop-1# : Bin → Bin⁺
  drop-1# 0#      = []
  drop-1# (bs 1#) = bs

  test-pred : Nat.pred =[ nats⁺ ] (pred ∘ drop-1#)
  test-pred = refl

  test-downFrom : List.map toℕ (downFrom testLimit) ≡
                  List.downFrom testLimit
  test-downFrom = refl
