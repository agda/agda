..
  ::
  module language.telescopes where

.. _telescopes:

**********
Telescopes
**********

.. note::
   This is a stub.


Irrefutable Patterns in Binding Positions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

..
  ::
  module pattern-tele where
    open import Agda.Builtin.Sigma
    open import Agda.Builtin.Equality
    private
      variable
        A : Set
        B : A → Set

Since Agda 2.6.1, irrefutable patterns can be used at every binding site in a
telescope to take the bound value of record type apart. The type of the second
projection out of a dependent pair will for instance naturally mention the value
of the first projection. Its type can be defined directly using an irrefutable
pattern as follows:

::

    proj₂ : ((a , _) : Σ A B) → B a

And this second projection can be implemented with a lamba-abstraction using
one of these irrefutable patterns taking the pair apart:

::

    proj₂ = λ (_ , b) → b

Using an as-pattern makes it possible to name the argument and to take it
apart at the same time. We can for instance prove that any pair is equal
to the pairing of its first and second projections, a property commonly
called eta-equality:

::

    eta : (p@(a , b) : Σ A B) → p ≡ (a , b)
    eta p = refl
