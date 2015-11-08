module Issue857 where

-- From the Agda mailing list, 2013-05-24, question raised by Martin Escardo.
-- 2013-05-24 reported by Martin Escardo, test case by Andrea Vezzosi

{- The crucial point is that λ() is not equal to λ(), so e.g. the
ones appearing in the body of main-closed-ground' don't match the ones
in its own type.

To be concrete we can use a simplified version of what happens in
main-closed-ground': -}

data ⊥ : Set where

postulate
    X : Set
    P : (⊥ → X) → Set
    lemma : (f : ⊥ → X) → P f

-- Given the context above we attempt to feed agda code using λ():

main : P λ()
main = lemma λ()

{- Before we can check the type of main we have to translate λ()
away into toplevel definitions, because internally only those are
allowed pattern-matching. But each use of λ() is translated
separately, so we get:

absurd1 : ⊥ → X
absurd1 ()

absurd2 : ⊥ → X
absurd2 ()

main : P absurd1
main = lemma absurd2

Now we can proceed typechecking and find that (lemma absurd2 : P
absurd2), i.e. applications of lemma only care about the type of its
argument, but for main to typecheck we need the type of the body (P
absurd2) to equal the declared type (P absurd1), and so we'd need
absurd2 = absurd1 which unfortunately we can't deduce because those
are different definitions.  -}


-- 2013-05-24 example by Martin Escardo

open import Common.Equality

absurd-equality : _≡_ {A = ⊥ → ⊥} (λ()) λ()
absurd-equality = refl

-- λ() is not translated as λ() → () (identity with variable name ())
-- thus, these examples should type check now.
