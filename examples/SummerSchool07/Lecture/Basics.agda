{-

          Types Summer School 2007

                 Bertinoro
             Aug 19 - 31, 2007


                   Agda

                Ulf Norell

-}

{-

  Learn more about Agda on the Agda wiki:

    http://www.cs.chalmers.se/~ulfn/Agda

  This is where you find the exercises for the afternoon.

-}

-- Each Agda file contains a top-level module, whose
-- name corresponds to the file name.

module Basics where

{-

  Expressions (types and terms)

-}

-- The expression language of Agda is your favorite dependently
-- typed λ-calculus.

-- For instance:
id₁ : (A : Set) -> A -> A
id₁ = \ A x -> x

id₂ : (A : Set) -> A -> A
id₂ = \ A x -> id₁ A (id₁ A x)

-- Note: Agda likes white space. This is not correct:
--   id:(A:Set)->A->A

-- Why not? In Agda the following strings are valid identifiers:
--   id:
--   A:Set
--   ->A->A

-- Another useful function, featuring telescopes
-- and typed λs.
compose : (A B C : Set) -> (B -> C) -> (A -> B) -> A -> C
compose = \(A B C : Set) f g x -> f (g x)

compose' : (A B : Set)(C : B -> Set)
           (f : (x : B) -> C x)(g : A -> B) ->
           (x : A) -> C (g x)
compose' = \A B C f g x -> f (g x)

{-

  Implicit arguments

-}

-- Writing down type arguments explicitly soon gets old.
-- Enter implicit arguments.

-- Note the curlies in the telescope. And A mysteriously disappeares
-- in the definition.
id₃ : {A : Set} -> A -> A
id₃ = \ x -> x

-- And it's not there when applying the function.
id₄ : {A : Set} -> A -> A
id₄ = \ x -> (id₃ (id₃ x))

-- If you think the type checker should figure out the value of
-- something explicit, you write _.
id₆ : {A : Set} -> A -> A
id₆ x = id₁ _ x

-- Interesting though it is, eventually you'll get bored
-- with the λ-calculus...

-- Move on to: Datatypes.agda
