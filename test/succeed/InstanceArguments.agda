module InstanceArguments where

postulate A₁ A₂ B : Set
          f₁ : {{a : A₁}} → B
          f₂ : {{a : A₂}} → B
          a₁ : A₁

-- resolve from signature
test₁ : B
test₁ = f₁

-- resolve from context
test₂ : {{a : A₂}} → B
test₂ = f₂

postulate F : Set → Set
          fA₁ : F A₁
          fA₂ : F A₂
          f₃ : {A : Set} → {{fA : F A}} → A → B

test₃ : B
test₃ = f₃ a₁

record Rec (t : Set) : Set₁ where
       field
         v : t

open module RecWI {t : Set} {{r : Rec t}} = Rec r

postulate testT₁ : Set 
          testV₁ : testT₁
          testT₂ : Set 
          testV₂ : testT₂

testRec₁ : Rec testT₁
testRec₁ = record { v = testV₁ }
testRec₂ : Rec testT₂
testRec₂ = record { v = testV₂ }

-- needs constraint checking in instance argument resolution
test : testT₂
test = v
