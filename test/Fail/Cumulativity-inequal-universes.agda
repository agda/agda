{-# OPTIONS --cumulativity #-}

open import Agda.Primitive
open import Agda.Builtin.Equality

lone ltwo lthree : Level
lone = lsuc lzero
ltwo = lsuc lone
lthree = lsuc ltwo

fails : _≡_ {a = lthree} {A = Set₂} Set₀ Set₁
fails = refl
