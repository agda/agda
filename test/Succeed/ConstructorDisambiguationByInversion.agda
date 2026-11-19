-- Disambiguate overloaded constructors when a type family is blocked on its index.
-- Agda can identify the constructor from the clauses or postpone the choice until a later argument.

module ConstructorDisambiguationByInversion where

open import Agda.Builtin.Bool using (Bool ; false ; true)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Unit using (⊤ ; tt)

data Other : Set where
  tt : Other

-- Agda cannot reduce `El` until its index is known.  The only clause of `El`
-- returns `⊤`, so Agda can rule out `Other.tt`.  Checking the remaining
-- constructor against the blocked type then determines the index.
module SingleResultHead where
  data Index : Set where
    only : Index

  El : Index → Set
  El only = ⊤

  index : ∀ {i} → El i → Index
  index {i} _ = i

  inferredIndex : Index
  inferredIndex = index tt  -- The sole result head admits only `Agda.Builtin.Unit.tt`.

  _ : inferredIndex ≡ only
  _ = refl

-- A unique constructor can be found even when the inversion map has several
-- result heads.  Of the possible types `⊤` and `Bool`, only `⊤` has a
-- constructor named `tt`, from which Agda can infer the index `false`.
module MultipleResultHeads where
  El : Bool → Set
  El false = ⊤
  El true  = Bool

  index : ∀ {i} → El i → Bool
  index {i} _ = i

  inferredIndex : Bool
  inferredIndex = index tt  -- Only `Agda.Builtin.Unit.tt` has one of the two result types.

  _ : inferredIndex ≡ false
  _ = refl

-- A constructor with an unapplied argument can have the function type returned
-- by `El`.  Comparing only the final result datatypes of the constructors
-- would discard `B.c`.  Checking `refl` determines that `B.c` is required
-- at type `A → B`.
module PartialApplication where
  data A : Set where
    c : A

  data B : Set where
    c : A → B

  El : Bool → Set
  El false = A
  El true  = A → B

  select : ∀ {i} → El i → i ≡ true → A → B
  select f refl = f

  test : A → B
  test = select c refl  -- The equality fixes the function type of `B.c`.

  _ : test A.c ≡ B.c A.c
  _ = refl

-- The `true` clause of `El` applies its parameter `F` to `true`, so the
-- result head of that clause is unknown.  Using only the head `⊤` from the
-- other clause would select the unit constructor.  After checking `refl`,
-- Agda knows the index is `true` and the expected type is `Other`.
module UnknownResultHead where
  El : (Bool → Set) → Bool → Set
  El F false = ⊤
  El F true  = F true

  select : ∀ {i} → El (λ _ → Other) i → i ≡ true → Other
  select t refl = t

  test : Other
  test = select tt refl  -- Once the index is known, `tt` is `Other.tt`.
