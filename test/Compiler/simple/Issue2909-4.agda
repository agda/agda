{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Char
open import Agda.Builtin.Coinduction
open import Agda.Builtin.IO
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.String

data Colist {a} (A : Set a) : Set a where
  []  : Colist A
  _∷_ : A → ∞ (Colist A) → Colist A

{-# FOREIGN GHC
  data Colist a    = Nil | Cons a (MAlonzo.RTE.Inf (Colist a))
  type Colist' l a = Colist a

  fromColist :: Colist a -> [a]
  fromColist Nil         = []
  fromColist (Cons x xs) = x : fromColist (MAlonzo.RTE.flat xs)
  #-}

{-# COMPILE GHC Colist = data Colist' (Nil | Cons) #-}

to-colist : ∀ {a} {A : Set a} → List A → Colist A
to-colist []       = []
to-colist (x ∷ xs) = x ∷ ♯ to-colist xs

a-definition-that-uses-♭ :
  ∀ {a} {A : Set a} → Colist A → Colist A
a-definition-that-uses-♭ []       = []
a-definition-that-uses-♭ (x ∷ xs) =
  x ∷ ♯ a-definition-that-uses-♭ (♭ xs)

postulate
  putStr : Colist Char → IO ⊤

{-# COMPILE GHC putStr = putStr . fromColist #-}

main : IO ⊤
main = putStr (a-definition-that-uses-♭
         (to-colist (primStringToList "apa\n")))
