****************
RsTHighlightCode
****************

..
Kenjiro:

    You're already dead!

::
   module RsTHighlightCode where

Shirou Emiya:

    People die when they're killed.

::
   data Bool : Set where
     true false : Bool

Keine:

    I've been waiting for you.

    Challenging me on the night of a full moon...
    You sure have guts.

::
   record Colist (A : Set) : Set where
     coinductive
     constructor _::_
     field
       cohead : A
       cotail : Colist A

Marisa:

    Good thing we're on a trial of guts anyway.

.. code-block:: agda

   record R : Set where
     field x : X

   module M where x = ...

   r : R
   r = record { M; z = ... }

Keine:

    You may not lay a single finger on her!

::
   open Colist

   postulate
     SomeSet : Set
     SomeVal : SomeSet

Mokou:

    Even Night Sparrows are drowned in the silence of the forest...
    I wasn't expecting to meet any humans here.

::
   {-# NON_TERMINATING #-}
   non-terminating-code-blocks : Colist SomeSet
   non-terminating-code-blocks =
       SomeVal :: non-terminating-code-blocks

Marisa:

    Who are you?

::
   open import Agda.Primitive
   variable i : Level

Alice:

    Marisa, this girl...

::
   copattern-definitions : Colist SomeSet
   cohead copattern-definitions = SomeVal
   cotail copattern-definitions = copattern-definitions

Mokou:

    I'm a human who's lived here for a long time...
    Don't worry, I'm not interested in eating you.

::
   import Agda.Builtin.List as List
   open List
   open import Agda.Builtin.Nat
     renaming (zero to O; suc to S)

Marisa:

    Human? Doesn't look like one.

::
   cotake : {A : Set} -> Nat -> Colist A -> List A
   cotake O _ = []
   cotake (S n) as = cohead as ∷ cotake n (cotail as)

Alice:

    Marisa, she's definitely human... but be careful.
