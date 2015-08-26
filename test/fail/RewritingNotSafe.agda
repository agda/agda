-- Andreas, 2015-08-26
{-# OPTIONS --rewriting #-} -- Should give error

open import Common.Equality

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE refl #-}
