-- {-# OPTIONS -v tc.term.let.pattern:20 #-}
-- {-# OPTIONS -v tc.meta.assign:10 #-}
-- {-# OPTIONS -v tc.meta.assign.proj:45 #-}
-- {-# OPTIONS -v tc.meta.assign.catch:80 #-}

-- Andreas, 2013-05-06 deep let-bound patterns were translated wrongly

module Issue843 {A B C : Set} (a : A) (b : B) (c : C) where

open import Common.Product
open import Common.Equality

T : Set
T = A × B × C

val : T
val = a , (b , c)

-- This was translated wrongly:
ap : {R : Set} (f : T → R) → R
ap f =
  let x , (y , z) = a , (b , c) -- val
  in f (x , (y , z))

works : {R : Set} (f : T → R) → R
works f =
  let x , yz = val
  in let y , z = yz
  in f (x , (y , z))

ap′ : {R : Set} (f : T → R) → R
ap′ f = f (proj₁ val , (proj₁ (proj₂ val) , proj₂ (proj₂ val)))

test : ∀ {R} (f : T → R) → ap f ≡ f (a , (b , c))
test f = refl

{- WAS:
The type of  test f  reduces to

Goal: f (a , proj₂ a , c) ≡ f (a , b , c)

even though it should reduce to

f (a , b , c) ≡ f (a , b , c)

And indeed, refl doesn't fit there. Typechecking the example where the hole has been replaced with refl produces:

D:\Agda\Strange.agda:21,10-14
proj₂ a != b of type B

when checking that the expression refl has type
ap f ≡ f (a , b , c)

With ap′, the goal reduces correctly and refl is accepted.


I'm using a development version of Agda, about one day old. 64bit Windows 7, if it matters.
-}
