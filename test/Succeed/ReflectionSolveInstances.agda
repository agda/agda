
-- See #4777

open import Agda.Builtin.Reflection renaming (bindTC to _>>=_; catchTC to _<|>_)
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

variable
  A B : Set
  F : Set → Set

_×_ : Set → Set → Set
A × B = Σ A λ _ → B

_>>_ : TC A → TC B → TC B
m >> m' = m >>= λ _ → m'

record HasShape (F : Set → Set) : Set₁ where
  field
    TheShape : Set
    shape    : F A → TheShape

Shape : (F : Set → Set) → ⦃ HasShape F ⦄ → Set
Shape F ⦃ i ⦄ = i .HasShape.TheShape

shape : ⦃ _ : HasShape F ⦄ → F A → Shape F
shape ⦃ i ⦄ = i .HasShape.shape

instance
  iShapeList : HasShape List
  iShapeList .HasShape.TheShape = Nat
  iShapeList .HasShape.shape [] = 0
  iShapeList .HasShape.shape (_ ∷ xs) = suc (iShapeList .HasShape.shape xs)

  iShapeMaybe : HasShape Maybe
  iShapeMaybe .HasShape.TheShape = Bool
  iShapeMaybe .HasShape.shape nothing  = false
  iShapeMaybe .HasShape.shape (just _) = true

pattern vArg ty = arg (arg-info visible (modality relevant quantity-ω)) ty

`Set = agda-sort (lit 0)

solveInstanceConstraintsIf : Bool → TC ⊤
solveInstanceConstraintsIf true  = solveInstanceConstraints
solveInstanceConstraintsIf false = returnTC _

macro
  -- Compute the reflected syntax of a normalised call to Shape ty.
  -- Run solveInstanceConstraints when the Bool is true.
  computeShape : Bool → Term → Term → TC ⊤
  computeShape solve ty hole = (do
      tyShape  ← checkType (def (quote Shape) (vArg ty ∷ [])) `Set
      noConstraints (solveInstanceConstraintsIf solve)
      `tyShape ← normalise tyShape >>= quoteTC
      unify hole `tyShape)
    <|> do
      `err ← quoteTC (Term.lit (string "computeShape failed"))
      unify hole `err

data Solution : Set where
  nat              : Solution
  unsolvedInstance : Solution
  failed           : String → Solution
  other            : Term → Solution

solution : Term → Solution
solution (def (quote Nat) [])                                       = nat
solution (def (quote HasShape.TheShape) (_ ∷ vArg (meta _ _) ∷ [])) = unsolvedInstance
solution (lit (string err))                                         = failed err
solution tm                                                         = other tm

-- Not solving instance constraints, we are left with an unsolved meta
-- for HasShape List.
_ : solution (computeShape false List) ≡ unsolvedInstance
_ = refl

-- Solving instance constraints. The constraint is resolved and we get Nat.
_ : solution (computeShape true List) ≡ nat
_ = refl

-- Failing to solve instance constraints. Caught by noConstraints.
_ : ⦃ _ : HasShape List ⦄ → solution (computeShape true List) ≡ failed "computeShape failed"
_ = refl

it : ⦃ x : A ⦄ → A
it ⦃ x ⦄ = x

-- Unsolved instance constraints from the outside do not cause noConstraints to fail.
_ : {P : Bool → Set} ⦃ iTrue : P true ⦄ ⦃ iFalse : P false ⦄
    (let b = _
         Pb : P b
         Pb = it  -- This is unsolved when we run the tactic
         sol = solution (computeShape true List)
    ) → (b ≡ false) × (sol ≡ nat)
_ = refl , refl
