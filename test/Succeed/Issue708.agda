
postulate
  String : Set

{-# BUILTIN STRING String #-}

record ⊤ : Set where
  constructor tt

data Bool : Set where
  true false : Bool

nonEmpty : String → Set
nonEmpty "" = Bool
nonEmpty _  = ⊤

foo : ∀ s → nonEmpty s → Bool
foo "" true  = true
foo "" false = false
foo s  p     = false
