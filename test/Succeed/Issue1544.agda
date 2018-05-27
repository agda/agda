-- Andreas, 2015-07-16 issue reported by G.Allais

-- This ought to pass, ideally, but the lack of positivity polymorphism
-- does not allow for a precise analysis of the composition operator.
--
-- Subsequently, the positivity analysis for tabulate returns no
-- positivity info for all arguments, leading to a rejection of
-- Command₃.

-- {-# OPTIONS -v tc.pos:10 #-}

open import Common.Product
open import Common.List

record ⊤ {a} : Set a where

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

postulate
  String : Set

USL = List String

data _∈_ a : USL → Set where
  z : ∀ {xs}             → a ∈ (a ∷ xs)
  s : ∀ {b xs} → a ∈ xs → a ∈ (b ∷ xs)

[Fields] : (args : USL) → Set₁
[Fields] []         =  ⊤
[Fields] (_ ∷ args) = Set × [Fields] args

[tabulate] : (args : USL) (ρ : {arg : _} (pr : arg ∈ args) → Set) → [Fields] args
[tabulate] []          ρ = _
[tabulate] (arg ∷ args) ρ = ρ z , [tabulate] args (λ x → ρ (s x))

[Record] : (args : USL) (f : [Fields] args) → Set
[Record] []          _        = ⊤
[Record] (hd ∷ args) (f , fs) = f × [Record] args fs

record Fields (args : USL) : Set₁ where
  constructor mkFields
  field
    fields : [Fields] args
open Fields public

record Record (args : USL) (f : Fields args) : Set where
  constructor mkRecord
  field
    content : [Record] args (fields f)
open Record public


module WORKS where

  tabulate : {args : USL} (ρ : {arg : _} (pr : arg ∈ args) → Set) → Fields args
  tabulate {args = args} ρ = mkFields ([tabulate] args ρ)  -- WORKS
  -- tabulate {args = args} = mkFields ∘ [tabulate] args -- FAILS

  mutual

    data Command₁ : Set where
      mkCommand : (modifierNames : USL) →
                  Record modifierNames (tabulate (λ {s} _ → Modifier s)) → Command₁

    record Command₂ : Set where
      inductive
      field
        modifierNames : USL
        modifiers     : [Record] modifierNames ([tabulate] _ (λ {s} _ → Modifier s))

    record Command₃ : Set where
      inductive
      field
        modifierNames : USL
        modifiers     : Record modifierNames (tabulate (λ {s} _ → Modifier s))

    data Modifier (name : String) : Set where
      command₁ : Command₁ → Modifier name
      command₂ : Command₂ → Modifier name
      command₃ : Command₃ → Modifier name


module FAILS where

  tabulate : {args : USL} (ρ : {arg : _} (pr : arg ∈ args) → Set) → Fields args
  -- tabulate {args = args} ρ = mkFields ([tabulate] args ρ)  -- WORKS
  tabulate {args = args} = mkFields ∘ [tabulate] args -- FAILS

  mutual

    data Command₁ : Set where
      mkCommand : (modifierNames : USL) →
                  Record modifierNames (tabulate (λ {s} _ → Modifier s)) → Command₁

    record Command₂ : Set where
      inductive
      field
        modifierNames : USL
        modifiers     : [Record] modifierNames ([tabulate] _ (λ {s} _ → Modifier s))

    record Command₃ : Set where
      inductive
      field
        modifierNames : USL
        modifiers     : Record modifierNames (tabulate (λ {s} _ → Modifier s))

    data Modifier (name : String) : Set where
      command₁ : Command₁ → Modifier name
      command₂ : Command₂ → Modifier name
      command₃ : Command₃ → Modifier name
