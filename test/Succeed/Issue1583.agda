-- Andreas, 2015-06-24 Parsing of forall should be like lambda

open import Common.Prelude
open import Common.Product

test : ⊤ × ∀ (B : Set) → B → B  -- should parse
test = _ , λ B b → b

test1 : ⊤ × forall (B : Set) → B → B  -- should parse
test1 = _ , λ B b → b
