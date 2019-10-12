-- Andreas, 2019-06-18, LAIM 2019, issue #3855:
-- Successful tests for the erasure (@0) modality.

module _ where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Coinduction

open import Common.IO

module WhereInErasedDeclaration where

  @0 n : Nat
  n = 4711

  @0 m : Nat
  m = n'
    where
    n' = n

module ErasedDeclarationInWhere where

  F : (G : @0 Set → Set) (@0 A : Set) → Set
  F G A = G B
    where
    @0 B : Set
    B = A

module FlatErasure where

  @0 resurrect-λ : (A : Set) (@0 x : A) → A
  resurrect-λ A = λ x → x

  -- Andreas, 2019-10-01:
  -- An extended lambda now lives in @ω by default,
  -- making this test fail.
  -- We need to find a way to tell when an extended lambda
  -- should be created in @0.  Often, when it is created
  -- in the type world, we still want to use it in the term
  -- world (in solutions found by the constraint solver).
  -- Thus, we cannot simply inherit the current quantity
  -- for the extended lambda.
  -- @0 resurrect-λ-where : (A : Set) (@0 x : A) → A
  -- resurrect-λ-where A = λ where x → x

  @0 resurrect-app : (A : Set) (@0 x : A) → A
  resurrect-app A x = x

module ErasedEquality where

  -- Should maybe not work --without-K
  -- should definitely not work in --cubical

  cast : ∀{A B : Set} → @0 A ≡ B → A → B
  cast refl x = x

  J : ∀{A : Set} {a : A} (P : (x : A) → a ≡ x → Set) {b : A}
      (@0 eq : a ≡ b) → P a refl → P b eq
  J P refl p = p

module ParametersAreErased where

  test : (@0 A : Set) → A ≡ A
  test A = refl {x = _}           -- TODO: A instead of _

module Records where

  record R (A : Set) : Set where
    field
      el : A
    Par : Set
    Par = A    -- record module parameters are NOT erased, so, this should be accepted

  proj : (A : Set) → R A → A  -- TODO: @0 A instead of A
  proj A r = R.el {A = _} r

  MyPar : (A : Set) → R A → Set
  MyPar A = R.Par {A = A}

  record RB (b : Bool) : Set where
    bPar : Bool
    bPar = b

  myBPar : (b : Bool) → RB b → Bool
  myBPar b r = RB.bPar {b = b} r

module CoinductionWithErasure (A : Set) where

  data Stream : Set where
    cons : (x : A) (xs : ∞ Stream) → Stream

  -- Andreas, 2019-10-01:
  -- A #-auxiliary function lives in @ω by default,
  -- making this test fail.

  -- @0 repeat : (@0 a : A) → Stream
  -- repeat a = cons a (♯ (repeat a))

main = putStrLn "Hello, world!"
