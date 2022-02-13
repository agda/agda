-- Andreas, 2021-07-14, issue #5470, reported by HarrisonGrodin
--
-- Importing a rewrite rule that was declared private
-- at the point of definition caused an internal error.

{-# OPTIONS --rewriting #-}

-- {-# OPTIONS -v impossible:10 #-}
-- {-# OPTIONS -v rewriting:100 #-}

module Issue5470 where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

open import Issue5470.Import

postulate
  _≤_ : (n m : Nat) → Set
  ≤-refl : ∀{n} → n ≤ n

infix 4 _IsRelatedTo_

data _IsRelatedTo_ (x : Nat) : (y : Nat) → Set where
  equals : x IsRelatedTo x

begin : ∀ {x y} → x IsRelatedTo y → x ≤ y
begin equals = ≤-refl

example : ∀ n → n ≤ bar n
example n = begin equals

-- WAS: internal error
-- Unbound name: Issue5470Import.lemma[0,10]@ModuleNameHash 8608063155492000951
