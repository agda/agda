{-# OPTIONS -vtc.decl:5 #-}
module Issue8134 (M : Set) where
open import Issue8134.M M
Should-not-be-rechecked : Set₁
Should-not-be-rechecked = Set
F : A → Set₁
F _ = Set
