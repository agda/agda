{-# OPTIONS --allow-unsolved-metas #-}

module _ where

postulate
  Functor : (Set → Set) → Set₁
  fmap : {F : Set → Set} {{_ : Functor F}} {A B : Set} → (A → B) → F A → F B

postulate
  Id : Set → Set

bla : {A : Set} → Id A → Id A
bla = fmap {{?}} (λ x → x) -- should not fail!
