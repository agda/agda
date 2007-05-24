{-

        Agda Implementors' Meeting VI

                  Göteborg
             May 24 - 30, 2007


                Hello Agda!

                Ulf Norell

-}

{-

   Getting your hands on Agda

   http://www.cs.chalmers.se/~ulfn/Agda

   darcs get --partial http://www.cs.chalmers.se/~ulfn/darcs/Agda2

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
compose : (A B C : Set)(f : B -> C)(g : A -> B) -> A -> C
compose = \(A B C : Set) -> \ f g x -> f (g x)

{-

  Implicit arguments

-}

-- Writing down type arguments explicitly soon gets old.
-- Enter implicit arguments.

-- Note the curlies in the telescope. And A mysteriously disappeared
-- in the definition.
id₃ : {A : Set} -> A -> A
id₃ = \ x -> x

-- And it's not there when applying the function.
id₄ : {A : Set} -> A -> A
id₄ = \ x -> (id₃ (id₃ x))

-- You can give implicit arguments explicitly.
id₅ : {A : Set} -> A -> A
id₅ {A} x = id₄ {A} x

-- If you want to give a particular implicit argument, you can refer
-- to it by name.
const : {A B : Set} -> A -> B -> A
const = \ x y -> x

const' : (A : Set) -> A -> A -> A
const' = \ A -> const {B = A}

-- It also works the other way around. If you think the type checker
-- should figure out the value of something explicit, you write _.
id₆ : {A : Set} -> A -> A
id₆ x = id₁ _ x

-- Interesting though it is, eventually you'll get bored
-- with the λ-calculus...

-- Move on to: Datatypes.agda
