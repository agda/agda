module Issue2469 where

open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.IO renaming (IO to BIO)
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Common.IO
open import Common.Prelude
open import Common.Sum
open import Common.Product


data F : Nat → Set where
  [] : F zero
  _∷1 : ∀ {n} → F n → F (suc n)
  _∷2 : ∀ {n} → F n → F (suc (suc n))

f : ∀ k → F (suc k) → F k ⊎ Maybe ⊥
f zero a = inj₂ nothing
f k (xs ∷1) = inj₂ nothing
-- to (suc k) xs = inj₂ nothing  -- This is fine
f (suc k) = λ xs → inj₂ nothing  -- This segfaults

myshow : F 1 ⊎ Maybe ⊥ → String
-- myshow (inj₁ b) = ""        -- This is fine
myshow (inj₁ (b ∷1)) = "bla"      -- This segfaults
myshow _ = "blub"

main : IO ⊤
main =  putStrLn (myshow (f 1 ([] ∷2)))
