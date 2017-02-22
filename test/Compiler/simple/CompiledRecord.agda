-- Andreas, 2015-08-18 Test case for COMPILED_DATA on record

-- open import Common.String
open import Common.IO

infixr 4 _,_
infixr 2 _×_

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_ public

{-# COMPILE GHC _×_ = data (,) ((,)) #-}

-- Note: could not get this to work for Σ.
-- Also, the universe-polymorphic version of _×_ would require more trickery.

swap : ∀{A B : Set} (p : A × B) → B × A
swap (x , y) = y , x

swap' : ∀{A B : Set} (p : A × B) → B × A
swap' p = proj₂ p , proj₁ p

main = putStrLn (proj₁ (swap (swap' (swap ("no" , "yes")))))
