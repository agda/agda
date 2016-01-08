-- Andreas, 2016-01-08 allow --type-in-type with universe polymorphism

{-# OPTIONS --type-in-type #-}

-- {-# OPTIONS --v tc:30 #-}
-- {-# OPTIONS --v tc.conv.level:60 #-}

open import Common.Level
open import Common.Equality

Type : Set
Type = Set

data E α β : Set β where
  e : Set α → E α β

data D {α} (A : Set α) : Set where
  d : A → D A

-- Make sure we do not get unsolved level metas

id : ∀{a}{A : Set a} → A → A
id x = x

test = id Set

data Unit : Set where
  unit : Unit

test1 = id unit

data UnitP {α} : Set α where
  unitP : UnitP

test2 = id unitP

-- All levels are equal
-- (need not be for --type-in-type, but this is how it is implemented):

level0≡1 : lzero ≡ lsuc lzero
level0≡1 = refl

levelTrivial : ∀{a b : Level} → a ≡ b
levelTrivial = refl
