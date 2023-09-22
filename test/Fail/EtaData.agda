-- Andreas, 2014-07-02 wondering about the ETA pragma (legacy?)

open import Common.Equality

data Prod (A B : Set) : Set where
  pair : A → B → Prod A B

{-# ETA Prod #-}

-- WAS: The ETA pragma does not exist anymore.

-- NOW as of 2023-08-30:
--
-- ETA pragma is only applicable to coinductive records
-- when checking the pragma ETA Prod

fst : {A B : Set} → Prod A B → A
fst (pair a b) = a

snd : {A B : Set} → Prod A B → B
snd (pair a b) = b

-- Just an illusion...
test : {A B : Set} (x : Prod A B) → x ≡ pair (fst x) (snd x)
test x = refl
