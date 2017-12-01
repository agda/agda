------------------------------------------------------------------------
-- The Agda standard library
--
-- Keys for AVL trees
-- The key type extended with a new minimum and maximum.
-----------------------------------------------------------------------

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_ ; refl)

module Data.AVL.Key
       {k r} (Key : Set k)
       {_<_ : Rel Key r}
       (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
       where

open IsStrictTotalOrder isStrictTotalOrder

open import Level
open import Data.Empty
open import Data.Unit
open import Data.Product

infix 5 [_]

data Key⁺ : Set k where
  ⊥⁺ ⊤⁺ : Key⁺
  [_]   : (k : Key) → Key⁺

[_]-injective : ∀ {k l} → [ k ] ≡ [ l ] → k ≡ l
[_]-injective refl = refl

-- An extended strict ordering relation.

infix 4 _<⁺_

_<⁺_ : Key⁺ → Key⁺ → Set r
⊥⁺    <⁺ [ _ ] = Lift ⊤
⊥⁺    <⁺ ⊤⁺    = Lift ⊤
[ x ] <⁺ [ y ] = x < y
[ _ ] <⁺ ⊤⁺    = Lift ⊤
_     <⁺ _     = Lift ⊥

-- A pair of ordering constraints.

infix 4 _<_<_

_<_<_ : Key⁺ → Key → Key⁺ → Set r
l < x < u = l <⁺ [ x ] × [ x ] <⁺ u

-- _<⁺_ is transitive.

trans⁺ : ∀ l {m u} → l <⁺ m → m <⁺ u → l <⁺ u

trans⁺ [ l ] {m = [ m ]} {u = [ u ]} l<m m<u = trans l<m m<u

trans⁺ ⊥⁺    {u = [ _ ]} _ _ = _
trans⁺ ⊥⁺    {u = ⊤⁺}    _ _ = _
trans⁺ [ _ ] {u = ⊤⁺}    _ _ = _

trans⁺ _     {m = ⊥⁺}    {u = ⊥⁺}    _ (lift ())
trans⁺ _     {m = [ _ ]} {u = ⊥⁺}    _ (lift ())
trans⁺ _     {m = ⊤⁺}    {u = ⊥⁺}    _ (lift ())
trans⁺ [ _ ] {m = ⊥⁺}    {u = [ _ ]} (lift ()) _
trans⁺ [ _ ] {m = ⊤⁺}    {u = [ _ ]} _ (lift ())
trans⁺ ⊤⁺    {m = ⊥⁺}                (lift ()) _
trans⁺ ⊤⁺    {m = [ _ ]}             (lift ()) _
trans⁺ ⊤⁺    {m = ⊤⁺}                (lift ()) _
