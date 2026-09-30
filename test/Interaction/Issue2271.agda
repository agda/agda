record Fun : Set₁ where
   field
     _⇒_ : Set → Set → Set
     K : Set

id : ∀{A : Set} → A → A
id x = x

data Unit : Set where
  u : Unit

data W (s : Unit) : Set where
  w : Unit → W s

variable
  F : Set
  m : Unit
  c : Unit

module R (E : Set) where
  module Param (fun : Fun) (open Fun fun) where

   test : ∀{A} → E → A ⇒ A
   test = {!aux!} -- C-c C-h

   test₂ : K → K
   test₂ k = {! id' (id k) !} -- C-c C-h

   test₃ : {A : Set} → A → A
   test₃ k = {! id'' ? !} -- C-c C-h

   test₄ : F → K → F
   test₄ = {! id''' !} -- C-c C-h

   T : Unit → Set
   T u = Unit

   test₅ : T m → Unit
   test₅ tm = {! id'''' tm !} -- C-c C-h

   test₆ : W m → W c → Unit
   test₆ (w x) = {! id'''' x !}
