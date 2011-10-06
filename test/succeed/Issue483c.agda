-- Andreas, 2011-10-06
module Issue483c where

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

record _×_ (A B : Set) : Set where
  constructor _,_
  field fst : A
        snd : B

postulate 
  A : Set
  f : .A → A

-- this succeeds
test : let X : .A → A
           X = _
       in .(x : A) → (X ≡ f) × (X (f x) ≡ f x)
test x = refl , refl

-- so this should also succeed
test2 : let X : .A → A
            X = _
        in .(x : A) → (X (f x) ≡ f x) × (X ≡ f)
test2 x = refl , refl
