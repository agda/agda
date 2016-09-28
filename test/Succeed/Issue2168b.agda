-- Andreas, 2016-09-19, issue #2168, reported by Nisse

-- {-# OPTIONS -v tc.cover:10 #-}
-- {-# OPTIONS -v tc.cover.splittree:30 -v tc.cc:40 -v tc.cover.split.con:30 #-}

open import Common.Equality

data Three : Set where
  one two three : Three

data Bool : Set where
  true false : Bool

P : Bool → Bool → Three
P z false = one
P false = λ _ → two  -- This caused internal error during clause compilation.
P z true = three

test-one : ∀ x → P x false ≡ one
test-one true  = refl
test-one false = refl

test-two : P false true ≡ two
test-two = refl

test-three : P true true ≡ three
test-three = refl
