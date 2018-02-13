------------------------------------------------------------------------
-- The Agda standard library
--
-- Fixed-size tables of values, implemented as functions from 'Fin n'.
-- Similar to 'Data.Vec', but focusing on ease of retrieval instead of
-- ease of adding and removing elements.
------------------------------------------------------------------------

module Data.Table where

open import Data.Table.Base public

open import Data.Bool using (true; false)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
import Function.Equality as FE
open import Function.Inverse using (Inverse; _↔_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

-- Changes the order of elements in the table according to a permutation (i.e.
-- an 'Inverse' object on the indices).

permute : ∀ {m n a} {A : Set a} → Fin m ↔ Fin n → Table A n → Table A m
permute π = rearrange (Inverse.to π FE.⟨$⟩_)


-- The result of 'select z i t' takes the value of 'lookup t i' at index 'i',
-- and 'z' everywhere else.

select : ∀ {n} {a} {A : Set a} → A → Fin n → Table A n → Table A n
lookup (select z i t) j with j ≟ i
... | yes _ = lookup t i
... | no  _ = z
