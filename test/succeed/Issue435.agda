-- {-# OPTIONS -v extendedlambda:100 -v int2abs.reifyterm.def:100 #-}
module Issue435 where

data Bool : Set where
  true false : Bool

record Unit : Set where

postulate
  Dh : ({ x : Bool } → Bool) → Set
  Di : ({{x : Bool}} → Bool) → Set

noth : Set
noth = Dh (\ { {true}  → false ; {false} → true})

noti : Set
noti = Di (\ { {{true}}  → false ; {{false}} → true})

-- Testing absurd patterns

data ⊥ : Set where

data T : Set where
  expl : (⊥ → ⊥) → T
  impl : ({_ : ⊥} → ⊥) → T
  inst : ({{_ : ⊥}} → ⊥) → T

explicit : T
explicit = expl (λ ())

implicit : T
implicit = impl (λ {})

instance : T
instance = inst (λ {{ }})

explicit-match : T
explicit-match = expl (λ { () })

implicit-match : T
implicit-match = impl (λ { {} })

implicit-match′ : T
implicit-match′ = impl (λ { { () } })

instance-match : T
instance-match = inst (λ { {{}} })

instance-match′ : T
instance-match′ = inst (λ { {{ () }} })
