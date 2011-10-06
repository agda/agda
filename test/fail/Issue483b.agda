-- Andreas, 2011-10-06
module Issue483b where

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

postulate 
  A : Set
  f : .A → A

test : let X : .A → A
           X = _
       in .(x : A) → X (f x) ≡ f x
test x = refl
-- this gave an internal error before because X _ = f x
-- was solved by X = λ _ → f __IMPOSSIBLE__
--
-- Now one should get an unsolved meta