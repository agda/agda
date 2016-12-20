-- Andreas, 2016-11-11 issue #2301,
-- reported by stedolan and fredrikNorvallForsberg:
-- compareTelescope ignored relevance.
-- Faulty behavior probably existed since 2011.

module Issue2301 where

data Box (A : Set) : Set where
  wrap : A → Box A

weird : ∀ A → .A → Box A
weird A = wrap

-- SHOULD FAIL with error:
-- A → Box A !=< .A → Box A
-- when checking that the expression wrap has type .A → Box A

-- WAS: checked.

-- Since the first argument to wrap is not actually irrelevant,
-- this lets us write a function that discards irrelevance annotations:

make-relevant : ∀ {A} → .A → A
make-relevant a = unwrap (weird a)
  where
    unwrap : ∀ {A} → Box A → A
    unwrap (wrap a) = a

-- or proves things we shouldn't:

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data Bool : Set where
  tt ff : Bool

absurd : {X : Set} → X
absurd {X} = different same
  where
    different : weird tt ≡ weird ff → X
    different ()

    irr-eq : ∀ {A B : Set} {x y : A} (f : .A → B) → f x ≡ f y
    irr-eq f = refl

    same : weird tt ≡ weird ff
    same = irr-eq weird
