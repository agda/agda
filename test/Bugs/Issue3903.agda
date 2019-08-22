
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.IO
open import Agda.Builtin.String

postulate
  putStr : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# COMPILE GHC putStr = Data.Text.IO.putStr #-}

data Sing : Nat → Set where
  sing : Sing zero

data Vec : Nat → Set where
  nil : Vec zero
  cons : ∀ n → Vec n → Vec (suc n)

isTailNil : ∀ m n → Sing m → Vec n → Bool
isTailNil .0 .1 sing (cons zero v) = true  -- two `zero`s are buried in the dot patterns, which to resurrect?
isTailNil _ _ _ _ = false

shouldBeFalse = isTailNil 0 2 sing (cons 1 (cons 0 nil))

isFalse : false ≡ shouldBeFalse
isFalse = refl

magic : false ≡ true → String
magic ()

f : (b : Bool) → false ≡ b → String
f false eq = "Phew!"
f true  eq = magic eq

main = putStr (f shouldBeFalse refl)
