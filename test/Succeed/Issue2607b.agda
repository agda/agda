{-# OPTIONS --overlapping-instances #-}

postulate
  Nat : Set
  Fin : Nat → Set
  Finnat : Nat → Set
  fortytwo : Nat
  finnatic : Finnat fortytwo
  _==_ : Finnat fortytwo → Finnat fortytwo → Set

record Fixer : Set where
  field fix : ∀ {x} → Finnat x → Finnat fortytwo
open Fixer {{...}}

postulate
  Fixidentity : {{_ : Fixer}} → Set
  instance
    fixidentity : {{fx : Fixer}} {{fxi : Fixidentity}} {f : Finnat fortytwo} → fix f == f

  InstanceWrapper : Set
  iwrap : InstanceWrapper
  instance
    IrrFixerInstance : .{{_ : InstanceWrapper}} → Fixer

instance
  FixerInstance : Fixer
  FixerInstance = IrrFixerInstance {{iwrap}}

instance
  postulate FixidentityInstance : Fixidentity

it : ∀ {a} {A : Set a} {{x : A}} → A
it {{x}} = x

fails : Fixer.fix FixerInstance finnatic == finnatic
fails = fixidentity

works : Fixer.fix FixerInstance finnatic == finnatic
works = fixidentity {{fx = it}}

works₂ : Fixer.fix FixerInstance finnatic == finnatic
works₂ = fixidentity {{fxi = it}}
