module FFI where

open import Common.Prelude


_+'_ : Nat → Nat → Nat
zero +' y = y
suc x +' y = suc (x +' y)
{-# COMPILE GHC _+'_ = (+) :: Integer -> Integer -> Integer #-}

-- on-purpose buggy haskell implementation!
_+''_ : Nat → Nat → Nat
zero +'' y = y
suc x +'' y = suc (x +'' y)
{-# COMPILE GHC _+''_ = (-) :: Integer -> Integer -> Integer #-}

listMap : {A B : Set} → (A → B) → List A → List B
listMap f [] = []
listMap f (x ∷ xs) = f x ∷ listMap f xs

{-# COMPILE GHC listMap as listMap #-}
{-# FOREIGN GHC
  agdaMap :: (a -> b) -> [a] -> [b]
  agdaMap = listMap () ()
#-}

open import Common.IO
open import Common.Unit

_>>_ : {A B : Set} → IO A → IO B → IO B
m >> m' = m >>= λ _ → m'

main : IO Unit
main = do
  printNat (10 +' 5)
  printNat (30 +'' 7)
