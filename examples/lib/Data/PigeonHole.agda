
module Data.PigeonHole where

open import Prelude
open import Data.Nat hiding (_==_; _<_)
open import Data.Fin
open import Data.Vec as Vec
open import Logic.Base
open import Logic.Identity

open Vec.Elem

tooManyPigeons : {n : Nat}(xs : Vec (Fin (suc n)) n) -> ∃ \p -> p ∉ xs
tooManyPigeons {zero}  [] = ∃-I fzero nl
tooManyPigeons {suc n} zs = aux zs (find _==_ fzero zs)
  where

    -- We start by checking whether or not fzero is an element of the list
    aux : {n : Nat}(xs : Vec (Fin (suc (suc n))) (suc n)) ->
          fzero ∈ xs \/ fzero ∉ xs -> ∃ \p -> p ∉ xs

    -- If it's not then we're done
    aux xs (\/-IR z∉xs) = ∃-I fzero z∉xs

    -- If it is we have to find another element
    aux xs (\/-IL z∈xs) = lem₂ ih
      where

        -- Let's remove the occurrence of fzero from the list and strip a fsuc
        -- from each of the other elements (i.e. map pred $ delete fzero xs)
        -- We can apply the induction hypothesis, giving us a p which is not in
        -- this list.
        ih : ∃ \p -> p ∉ map pred (delete fzero xs z∈xs)
        ih = tooManyPigeons (map pred $ delete _ xs z∈xs)

        -- First observe that if i ∉ map pred xs then fsuc i ∉ xs. Using this
        -- lemma we conclude that fsuc p ∉ delete fzero xs.
        lem₀ : {n m : Nat}(i : Fin (suc n))(xs : Vec (Fin (suc (suc n))) m) ->
              i ∉ map pred xs -> fsuc i ∉ xs
        lem₀ i []      nl       = nl
        lem₀ i (x :: xs) (cns h t) = cns (rem₀ h) (lem₀ i xs t)
          where
            rem₀ : {n : Nat}{i : Fin (suc n)}{j : Fin (suc (suc n))} ->
                   i ≢ pred j -> fsuc i ≢ j
            rem₀ i≠i refl = i≠i refl

        -- Furthermore, if i ∉ delete j xs and i ≠ j then i ∉ xs.
        lem₁ : {n m : Nat}{i : Fin (suc n)}{j : Fin n}
               (xs : Vec (Fin (suc n)) (suc m))(p : i ∈ xs) ->
               thin i j ∉ delete i xs p -> thin i j ∉ xs
        lem₁ (x :: xs)  hd    el = cns (thin-ij≠i _ _) el
        lem₁ {m = zero } (x :: xs) (tl ()) _
        lem₁ {m = suc _} (x :: xs) (tl p) (cns h t) = cns h (lem₁ xs p t)

        -- So we get fsuc p ∉ xs and we're done.
        lem₂ : (∃ \p -> p ∉ map pred (delete fzero xs z∈xs)) ->
               (∃ \p -> p ∉ xs)
        lem₂ (∃-I p h) = ∃-I (fsuc p) (lem₁ xs z∈xs $ lem₀ _ _ h)

-- tooManyHoles : {n : Nat}(xs : Vec (Fin n) (suc n)) ->
--             ∃ \p -> ∃ \i -> ∃ \j -> xs ! i ≡ p /\ xs ! thin i j ≡ p
-- tooManyHoles = ?

