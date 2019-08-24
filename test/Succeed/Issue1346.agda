-- Andreas, 2019-08-17, issue #1346

-- Allow changing fixity in renaming statement

module Issue1346 where

data Bool : Set where true false : Bool

module Product where

  infixr 4 _,_

  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B

module List where

  infixr 5 _∷_

  data List (A : Set) : Set where
    []  : List A
    _∷_ : A → List A → List A

open List public hiding (module List)
open Product public using () renaming
  ( _,_ to infixr 5 _∷_   -- change binding strength of _,_ when imported as _∷_
  ; _×_ to infixr 8 _×_   -- make _×_ right associatives
  )

-- Non-empty lists.

List⁺ : Set → Set
List⁺ A = A × List A

head : ∀{A} → List⁺ A → A
head (a ∷ as) = a

private
  test₁ : List⁺ Bool
  test₁ = true ∷ false ∷ []  -- mixing _∷_ of _×_ and List

open Product public using (_,_)  -- _,_ is still available with original fixity

private
  test₂ : ∀{A : Set} → A → List A × List⁺ A × List⁺ A
  test₂ a = [] , a ∷ [] , a ∷ a ∷ []  -- mixing _,_ and _∷_ of _×_
