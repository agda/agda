-- Bug: With abstraction depended on bound variable names!
module Issue233 where

postulate
  T   : (Set → Set) → Set
  mkT : (F : Set → Set) → T F

foo : T (λ A → A)
foo with λ (B : Set) → B
... | F = mkT F
