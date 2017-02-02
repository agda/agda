-- Andreas, 2015-08-26
{-# OPTIONS --rewriting #-} -- Should give error

open import Agda.Builtin.Equality
open import Common.List

{-# BUILTIN REWRITE _≡_ #-}

lengthMap : {A B : Set} (f : A → B) (xs : List A) →
            length (map f xs) ≡ length xs
lengthMap f [] = refl
lengthMap f (x ∷ xs) rewrite lengthMap f xs = refl

{-# REWRITE lengthMap #-}
