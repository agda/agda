{-# OPTIONS -v treeless.opt:20 -v treeless.opt.unused:30 #-}

module _ where

open import Common.Prelude

-- First four arguments are unused.
maybe : ∀ {a b} {A : Set a} {B : Set b} → B → (A → B) → Maybe A → B
maybe z f nothing = z
maybe z f (just x) = f x

mapMaybe : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Maybe A → Maybe B
mapMaybe f x = maybe nothing (λ y → just (f y)) x

maybeToNat : Maybe Nat → Nat
maybeToNat m = maybe 0 (λ x → x) m

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr f z [] = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

main : IO Unit
main = printNat (maybeToNat (just 42))
    ,, printNat (maybeToNat (mapMaybe (10 +_) (just 42)))
    ,, printNat (foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ []))
