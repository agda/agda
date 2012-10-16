module ExtendedLambdaCase where

data Bool : Set where
  true false : Bool

data Void : Set where

foo : Bool -> Bool -> Bool -> Bool
foo = λ { x → λ { y z → {!!} } }

module parameterised {A : Set}(B : A -> Set) where

  data Bar : (Bool -> Bool) -> Set where
    baz : (t : Void) -> Bar λ { x → {!!} }

  -- with hidden argument
  data Bar' : (Bool -> Bool) -> Set where
    baz' : {t : Void} -> (t' : Void) -> Bar' λ { x' → {!!} }


baz : Bool -> {w : Bool} -> Bool
baz = λ { z {w} → {!!} }

another-short-name : {A : Set} -> (A -> {x : A} -> A -> A)
another-short-name = {! λ { a {x} b → a } !}

f : Set
f =  (y : Bool) -> parameterised.Bar {Bool}(λ _ → Void) (λ { true → true ; false → false })


