-- Andreas, 2015-08-27 Allow rewrite rules for symbols defined in other file

{-# OPTIONS --rewriting --confluence-check #-}

open import Common.Nat
open import Common.Equality

{-# BUILTIN REWRITE _≡_ #-}

x+0 : ∀ x → x + 0 ≡ x
x+0 zero = refl
x+0 (suc x) rewrite x+0 x = refl

{-# REWRITE x+0 #-}  -- adding rewrite rule for + is ok

x+0+0 : ∀{x} → (x + 0) + 0 ≡ x
x+0+0 = refl
