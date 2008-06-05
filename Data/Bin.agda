------------------------------------------------------------------------
-- A binary representation of natural numbers
------------------------------------------------------------------------

module Data.Bin where

import Data.Nat as Nat
open Nat using (ℕ)
open import Data.Digit
import Data.Fin as Fin
open Fin using (Fin; zero; Fin-decSetoid)
open import Data.Fin.Props using (addFin')
open import Data.List
import Data.Vec as Vec
open import Data.Function
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
import Data.List.Equality as ListEq
private
  module DecEq  = DecSetoid (ListEq.DecidableEquality.decSetoid
                               (Fin-decSetoid 2))
  module PropEq = ListEq.PropositionalEquality (Fin 2)

------------------------------------------------------------------------
-- The type

-- A representation of binary natural numbers in which there is
-- exactly one representative for every number.

-- The function toℕ below defines the meaning of Bin.

infix 8 _1#

data Bin : Set where
  -- Zero.
  0#  : Bin
  -- bs 1# stands for the binary number 1<reverse bs>.
  _1# : [ Bit ] -> Bin

------------------------------------------------------------------------
-- Conversion functions

-- Converting to a list of bits starting with the _least_ significant
-- one.

toBits : Bin -> [ Bit ]
toBits 0#      = singleton 0b
toBits (bs 1#) = bs ++ singleton 1b

-- Converting to a natural number.

toℕ : Bin -> ℕ
toℕ = fromDigits ∘ toBits

-- Converting from a list of bits, starting with the _most_
-- significant one.

fromBits' : [ Bit ] -> Bin
fromBits' []                  = 0#
fromBits' (zero         ∷ bs) = fromBits' bs
fromBits' (Fin.suc zero ∷ bs) = reverse bs 1#
fromBits' (Fin.suc (Fin.suc ()) ∷ _)

-- Converting from a list of bits, starting with the _least_
-- significant one.

fromBits : [ Bit ] -> Bin
fromBits = fromBits' ∘ reverse

-- Converting from a natural number.

fromℕ : ℕ -> Bin
fromℕ n                with toDigits 2 n
fromℕ .(fromDigits bs) | digits bs = fromBits bs

------------------------------------------------------------------------
-- Queries

infix 4 _Bin-≟_

_Bin-≟_ : Decidable {Bin} _≡_
0#     Bin-≟ 0#     = yes ≡-refl
bs₁ 1# Bin-≟ bs₂ 1# with DecEq._≟_ bs₁ bs₂
... | yes eq = yes (≡-cong _1# (PropEq.ListEq⇒≡ eq))
... | no ¬eq = no (¬eq ∘ DecEq.reflexive ∘ helper)
  where
  helper : forall {bs₁ bs₂} -> bs₁ 1# ≡ bs₂ 1# -> bs₁ ≡ bs₂
  helper ≡-refl = ≡-refl
0# Bin-≟ bs₂ 1# = no helper
  where
  helper : ¬ 0# ≡ bs₂ 1#
  helper ()
bs₁ 1# Bin-≟ 0# = no helper
  where
  helper : ¬ bs₁ 1# ≡ 0#
  helper ()

Bin-decSetoid : DecSetoid
Bin-decSetoid = ≡-decSetoid _Bin-≟_

------------------------------------------------------------------------
-- Arithmetic

-- Multiplication by 2.

infix 7 _*2 _*2+1

_*2 : Bin -> Bin
0#      *2 = 0#
(bs 1#) *2 = (0b ∷ bs) 1#

_*2+1 : Bin -> Bin
0#      *2+1 = [] 1#
(bs 1#) *2+1 = (1b ∷ bs) 1#

-- Division by 2, rounded downwards.

⌊_/2⌋ : Bin -> Bin
⌊ 0#          /2⌋ = 0#
⌊ [] 1#       /2⌋ = 0#
⌊ (b ∷ bs) 1# /2⌋ = bs 1#

private
 module Dummy where

  open Fin using (suc)

  -- Addition.

  Carry : Set
  Carry = Bit

  addBits : Carry -> Bit -> Bit -> Carry × Bit
  addBits c b₁ b₂ with addFin' c (addFin' b₁ b₂)
  ... | zero                 = (0b , 0b)
  ... | suc zero             = (0b , 1b)
  ... | suc (suc zero)       = (1b , 0b)
  ... | suc (suc (suc zero)) = (1b , 1b)
  ... | suc (suc (suc (suc ())))

  addCarryToBitList : Carry -> [ Bit ] -> [ Bit ]
  addCarryToBitList zero       bs              = bs
  addCarryToBitList (suc zero) []              = 1b ∷ []
  addCarryToBitList (suc zero) (zero     ∷ bs) = 1b ∷ bs
  addCarryToBitList (suc zero) (suc zero ∷ bs) = 0b ∷ addCarryToBitList 1b bs
  addCarryToBitList (suc (suc ())) _
  addCarryToBitList _ (suc (suc ()) ∷ _)

  addBitLists : Carry -> [ Bit ] -> [ Bit ] -> [ Bit ]
  addBitLists c []         bs₂        = addCarryToBitList c bs₂
  addBitLists c bs₁        []         = addCarryToBitList c bs₁
  addBitLists c (b₁ ∷ bs₁) (b₂ ∷ bs₂) with addBits c b₁ b₂
  ... | (c' , b') = b' ∷ addBitLists c' bs₁ bs₂

  infixl 6 _+_

  _+_ : Bin -> Bin -> Bin
  m + n = fromBits (addBitLists 0b (toBits m) (toBits n))

  -- Multiplication.

  infixl 7 _*_

  _*_ : Bin -> Bin -> Bin
  0#                 * n = 0#
  []              1# * n = n
  -- (b + 2 * bs 1#) * n = b * n + 2 * (bs 1# * n)
  (b        ∷ bs) 1# * n with bs 1# * n
  (b        ∷ bs) 1# * n | 0#     = 0#
  (zero     ∷ bs) 1# * n | bs' 1# = (0b ∷ bs') 1#
  (suc zero ∷ bs) 1# * n | bs' 1# = n + (0b ∷ bs') 1#
  (suc (suc ()) ∷ _) 1# * _ | _

open Dummy public

-- Successor.

suc : Bin -> Bin
suc n = [] 1# + n

-- Division by 2, rounded upwards.

⌈_/2⌉ : Bin -> Bin
⌈ n /2⌉ = ⌊ suc n /2⌋
