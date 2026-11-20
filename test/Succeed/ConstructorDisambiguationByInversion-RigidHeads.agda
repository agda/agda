-- An overloaded constructor can be selected when some clauses of the blocked
-- type return a universe, a bound type variable, or a postulated type.

module ConstructorDisambiguationByInversion-RigidHeads where

open import Agda.Builtin.Bool using (Bool ; false ; true)
open import Agda.Builtin.Equality using (_≡_ ; refl)

data A : Set₁ where
  c : A

data B : Set₁ where
  c : B

index : (El : Bool → Set₁) → ∀ {i} → El i → Bool
index El {i} _ = i

-- Both constructors produce elements of datatypes.  Neither can serve as a
-- type in the universe returned by the second clause.
module Universe where
  El : Bool → Set₁
  El false = A
  El true  = Set

  inferredIndex : Bool
  inferredIndex = index El c  -- Only `A.c` can have type `El _`.

  _ : inferredIndex ≡ false
  _ = refl

postulate P : Set₁

-- The inversion map for this definition records the postulated type directly.
-- Neither constructor belongs to that type.
module PostulatedType where
  El : Bool → Set₁
  El false = A
  El true  = P

  inferredIndex : Bool
  inferredIndex = index El c  -- The clause returning `A` admits `A.c`.

  _ : inferredIndex ≡ false
  _ = refl

-- The second clause returns a parameter.  Its result head depends on the
-- argument supplied to `El` at the constructor occurrence.
module TypeParameter where
  El : Set₁ → Bool → Set₁
  El X false = A
  El X true  = X

  -- At this occurrence Agda instantiates the parameter in the inversion map
  -- with the bound variable `X`.  Solving the unknown index cannot instantiate `X`.
  module BoundVariable (X : Set₁) where
    inferredIndex : Bool
    inferredIndex = index (El X) c  -- Neither constructor targets `X`, leaving `A.c`.

    _ : inferredIndex ≡ false
    _ = refl

  -- Applying `F` to `true` still leaves the bound variable `F` at the head.
  -- In this context the application cannot reduce to either constructor’s datatype.
  module AppliedVariable (F : Bool → Set₁) where
    inferredIndex : Bool
    inferredIndex = index (El (F true)) c  -- The type `F true` is neutral, leaving `A.c`.

    _ : inferredIndex ≡ false
    _ = refl

  -- In `PostulatedType` the postulate occurs in a clause body.  Here it first
  -- appears in the inversion map when Agda substitutes the argument `P`.
  module PostulatedArgument where
    inferredIndex : Bool
    inferredIndex = index (El P) c  -- Supplying `P` for the parameter leaves `A.c`.

    _ : inferredIndex ≡ false
    _ = refl

-- While checking `inferredIndex`, Agda knows only the signature of `X`.
-- The later definition of `X` and the equality fixing the index to `true`
-- make `B` the expected type of the constructor.
module ForwardDefinition where
  open TypeParameter using (El)

  mutual
    X : Set₁

    inferredIndex : Bool
    inferredIndex = index (El X) c  -- Postponing the choice allows `B.c`.

    X = B

    computed : inferredIndex ≡ true
    computed = refl
