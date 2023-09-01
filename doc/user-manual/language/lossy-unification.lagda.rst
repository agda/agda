.. _lossy-unification:


*****************
Lossy Unification
*****************

The option :option:`--lossy-unification` enables an
experimental heuristic in the unification checker intended to improve
its performance for unification problems of the form ``f es₀ = f es₁``,
i.e. unifying two applications of the same defined function, here
``f``, to possibly different lists of arguments and projections
``es₀`` and ``es₁``.
The heuristic is sound but not complete.
In particular if Agda accepts code with the flag enabled it should
also accept it without the flag (with enough resources, and possibly
needing extra type annotations).

The option can be used either globally or in an ``OPTIONS`` pragma, in the latter
case it applies only to the current module.


Heuristic
~~~~~~~~~

When trying to solve the unification problem ``f es₀ = f es₁`` the
heuristic proceeds by trying to solve ``es₀ = es₁``, if that succeeds
the original problem is also solved, otherwise unification proceeds as
without the flag, likely by reducing both ``f es₀`` and ``f es₁``.


Example
~~~~~~~

Suppose ``f`` adds ``100`` to its input as defined below

.. code-block:: agda

  f : ℕ → ℕ
  f n = 100 + n

then to unify ``f 2`` and ``f (1 + 1)`` the heuristic would proceed by
unifying ``2`` with ``(1 + 1)``, which quickly succeeds. Without the
flag we might instead first reduce both ``f 2`` and ``f (1 + 1)`` to
``102`` and then compare those results.

The performance will improve most dramatically when reducing an
application of ``f`` would produce a large term, perhaps an element of
a record type with several fields and/or large embedded proof terms.



Drawbacks
~~~~~~~~~

One drawback is that in some cases performance of
unification will be worse with the heuristic. Specifically, if
the heuristic will repeatedly attempt to unify lists of arguments ``es₀
= es₁`` while failing.

The main drawback is that the heursitic is not complete, i.e. it will cause Agda to
ignore some possible solutions to unification variables.
For example if ``f`` is a constant function, then the constraint ``f
?0 = f 1`` does not uniquely determine ``?0``, but the heuristic will
end up assigning ``1`` to ``?0``.

Such assignments can lead to Agda to report a type error which would
not have been reported without the heuristic. This is because committing to
``?0 = 1`` might make other constraints unsatifiable.

Such assignments might also confuse readers. Note that with non-lossy
unification you have the guarantee (in the absence of bugs) that, if
the code type-checks, and you can find one consistent way to
instantiate all meta-variables, then that is the way that the code is
interpreted by the system. With lossy unification the solution you
have in mind might not be the one the system uses.

Consider the following code, which is based on an example from López
Juan's `PhD thesis <https://research.chalmers.se/publication/527051>`_
(see Listing 6.16):

::

  {-# OPTIONS --lossy-unification #-}

..
  ::
  module language.lossy-unification where

::

  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat

  private variable
    m n : Nat

  infixr 5 _∷_ _++_

  data Bit-vector : Nat → Set where
    []  : Bit-vector 0
    _∷_ : Bool → Bit-vector n → Bit-vector (suc n)

  _++_ : Bit-vector m → Bit-vector n → Bit-vector (m + n)
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  replicate : ∀ n → Bool → Bit-vector n
  replicate zero    x = []
  replicate (suc n) x = x ∷ replicate n x

  vector : Bit-vector (m + n)
  vector {m = m} {n = n} = replicate m true ++ replicate n false

Can you confidently predict the values of all of the following four
bit-vectors? Are you sure that readers of your code can do this?

::

  ex₁ : Bit-vector (0 + 1)
  ex₁ = vector

  ex₂ : Bit-vector (1 + 0)
  ex₂ = vector

  ex₃ : Bit-vector ((0 + 1) + (1 + 0))
  ex₃ = xs ++ xs
    where
    xs = vector

  ex₄ : Bit-vector ((0 + 1) + (1 + 0))
  ex₄ = xs ++ xs
    where
    xs = vector {m = _}

References
----------

Slow typechecking of single one-line definition, `issue (#1625) <https://github.com/agda/agda/issues/1625>`_.
