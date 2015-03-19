module Issue846.Imports where

open import Data.Nat public using (ℕ; zero; suc; _≤_; _∸_)
open import Data.List public using (List; []; _∷_)
open import Data.Bool public using (Bool; true; false; not)
open import Issue846.OldDivMod public using (_mod_)
open import Data.Fin public using (Fin; toℕ; zero; suc)
open import Relation.Binary.PropositionalEquality public using (_≡_; _≢_; cong)

open import Relation.Binary public using (nonEmpty) -- this is the bad guy

open import Issue846.DivModUtils public using (1'; lem-sub-p)

record Move : Set where
  constructor pick
  field
    picked : ℕ
    1≤n    : 1 ≤ picked
    n≤6    : picked ≤ 6
open Move using (picked)

Strategy = ℕ → Move

{-# TERMINATING #-}
play : ℕ → Strategy → Strategy → List ℕ
play 0 _ _ = []
play n p1 p2 = n ∷ play (n ∸ picked (p1 n)) p2 p1

postulate
  opt : Strategy

evenList : {A : Set} → List A → Bool
evenList [] = true
evenList (_ ∷ xs) = not (evenList xs)

winner : ℕ → Strategy → Strategy → Bool
winner n p1 p2 = evenList (play n p1 p2)

postulate
  opt-is-opt : ∀ n s → n mod 7 ≢ 1' → winner n opt s ≡ true
