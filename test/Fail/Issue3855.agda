-- Andreas, 2019-06-17, LAIM 2019, issue #3855
-- Only allow erased definitions (such as projections of erased fields)
-- in erased context.

{-# OPTIONS --erasure #-}

open import Common.IO
open import Common.Unit
open import Common.String
open import Common.Bool

record Erased (A : Set) : Set where
  constructor erase
  field
    @0 gone : A

noWorld : Bool → Erased String
noWorld true  = erase "Hello world!"
noWorld false = erase "Hallo, Welt!"

-- Illegal definition, should raise a type error.

unerase : ∀{A : Set} → Erased A → A
unerase = Erased.gone

main = putStrLn (unerase (noWorld false))

-- WAS: type checker let it through, compiler produces ill-formed Haskell
