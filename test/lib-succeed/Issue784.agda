-- From Dimytro Starosud
-- https://github.com/dima-starosud/Uniqueness-typing-in-Agda/blob/master/RefAPITest.agda
module Issue784 where

open import Issue784.RefAPI

open import Function
open import Data.Nat
open import Data.Product

-- new : ∀ a n → Transformer! [] [(n , Unique (Ref-ℕ a))]
{-Here also doesn't work without type constraint.
  Note: that type is exactly the same as of new-ℕ !!!
-}
new = new-ℕ
_++ = inc-ℕ
*_ = get-ℕ
free = free-ℕ

tr : (n : ℕ) → Transformer! [] [(_ , Pure (Exact $ suc n))]
tr i = "r" := new i ⇒⟦ refl ⟧⇒  -- new ℕ(i)
       "r" ++       ⇒⟦ refl ⟧⇒  -- r++
       "j" := * "r" ⇒⟦ refl ⟧⇒  -- j := *r
       free "r"

p : ∀ n → getExact (extract $ tr n) ≡ suc n
p = ≡-exact ∘ extract ∘ tr
