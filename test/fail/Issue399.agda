-- 2011-04-12 AIM XIII fixed this issue by freezing metas after declaration (Andreas & Ulf)

module Issue399 where

open import Common.Prelude

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

record MyMonadPlus m : Set₁ where
   field mzero : {a : Set} → m a → List a
         mplus : {a : Set} → m a → m a → List a
-- this produces an unsolved meta variable, because it is not clear which
-- level m has.  m could be in Set -> Set or in Set -> Set1
-- if you uncomment the rest of the files, you get unsolved metas here

{- Old error, without freezing:
--Emacs error: and the 10th line is the above line
--/home/j/dev/apps/haskell/agda/learn/bug-in-record.agda:10,36-39
--Set != Set₁
--when checking that the expression m a has type Set₁
-}

mymaybemzero : {a : Set} → Maybe a → List a
mymaybemzero nothing = []
mymaybemzero (just x) = x ∷ []

mymaybemplus : {a : Set} → Maybe a → Maybe a → List a
mymaybemplus x y = (mymaybemzero x) ++ (mymaybemzero y)

-- the following def gives a type error because of unsolved metas in MyMonadPlus
-- if you uncomment it, you see m in MyMonadPlus yellow
mymaybeMonadPlus : MyMonadPlus Maybe
mymaybeMonadPlus = record { mzero = mymaybemzero
                           ; mplus = mymaybemplus }

