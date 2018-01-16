open import Agda.Builtin.Char
open import Agda.Builtin.Coinduction
open import Agda.Builtin.IO
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.String

data Colist {a} (A : Set a) : Set a where
  []  : Colist A
  _∷_ : A → ∞ (Colist A) → Colist A

{-# FOREIGN GHC type Colist a b = [b] #-}
{-# COMPILE GHC Colist = data Colist ([] | (:)) #-}

toColist : ∀ {a} {A : Set a} → List A → Colist A
toColist []       = []
toColist (x ∷ xs) = x ∷ ♯ toColist xs

postulate
  putStr : Colist Char → IO ⊤

{-# COMPILE GHC putStr = putStr #-}

main : IO ⊤
main = putStr (toColist (primStringToList "apa\n"))
