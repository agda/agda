..
  ::

  module language.runtime-irrelevance where

  open import Agda.Primitive
  open import Agda.Builtin.Nat
  open import Agda.Builtin.Equality
  open import Agda.Builtin.List

  private
    variable
      a b : Level
      A : Set a

.. _runtime-irrelevance:

********************
Run-time Irrelevance
********************

From version 2.6.1 Agda supports run-time irrelevance (or erasure) annotations. Values marked as
erased are not present at run time, and consequently the type checker enforces that no computations
depend on erased values.

Syntax
======

A function or constructor argument is declared erased using the ``@0`` or ``@erased`` annotation.
For example, the following definition of vectors guarantees that the length argument to ``_∷_`` is not
present at runtime::

  data Vec (A : Set a) : Nat → Set a where
    []  : Vec A 0
    _∷_ : ∀ {@0 n} → A → Vec A n → Vec A (suc n)

The :ref:`GHC backend <ghc-backend>` compiles this to a datatype where the cons constructor takes only two
arguments.

.. note::
  In this particular case, the compiler identifies that the length argument can be erased also without the
  annotation, using Brady et al's forcing analysis :ref:`[1] <references>`. Marking it erased explictly, however,
  ensures that it is erased without relying on the analysis.

Erasure annotations can also appear in function arguments (both first-order and higher-order). For instance, here is
an implementation of ``foldl`` on vectors::

  foldl : (B : Nat → Set b)
        → (f : ∀ {@0 n} → B n → A → B (suc n))
        → (z : B 0)
        → ∀ {@0 n} → Vec A n → B n
  foldl B f z []       = z
  foldl B f z (x ∷ xs) = foldl (λ n → B (suc n)) (λ {n} → f {suc n}) (f z x) xs

Here the length arguments to ``foldl`` and to ``f`` have been marked erased. As a result it gets compiled to the following
Haskell code (modulo renaming):

.. code-block:: text

  foldl f z xs
    = case xs of
        []     -> z
        x ∷ xs -> foldl f (f _ z x) xs

In contrast to constructor arguments, erased arguments to higher-order functions are not removed completely, but
instead replaced by a placeholder value ``_``. The crucial optimization enabled by the erasure annotation is compiling
``λ {n} → f {suc n}`` to simply ``f``, removing a terrible space leak from the program. Compare to the result of
compiling without erasure:

.. code-block:: text

  foldl f z xs
    = case xs of
        []     -> z
        x ∷ xs -> foldl (\ n -> f (1 + n)) (f 0 z x) xs

It is also possible to mark top-level definitions as erased. This guarantees that they are only used in erased arguments
and can be useful to ensure that code intended only for compile-time evaluation is not executed at run time. For instance,

::

  @0 spec : Nat → Nat   -- slow, but easy to verify
  impl    : Nat → Nat   -- fast, but hard to understand
  proof   : ∀ n → spec n ≡ impl n

..
  ::
  spec n = n
  impl n = n
  proof n = refl

Erased record fields become erased arguments to the record constructor and the projection functions
are treated as erased definitions.

Rules
=====

The typing rules are based on Conor McBride's "I Got Plenty o’Nuttin’" :ref:`[2] <references>` and
Bob Atkey's "The Syntax and Semantics of Quantitative Type Theory" :ref:`[3] <references>`. In
essence the type checker keeps track of whether it is running in *run-time mode*, checking something
that is needed at run time, or *compile-time mode*, checking something that will be erased. In
compile-time mode everything to do with erasure can safely be ignored, but in run-time mode the
following restrictions apply:

- Cannot use erased variables or definitions.
- Cannot pattern match on erased arguments, unless there is at most
  one valid case. If ``--without-K`` is enabled and there is one valid
  case, then the datatype must also not be indexed.

Consider the function ``foo`` taking an erased vector argument::

  foo : (n : Nat) (@0 xs : Vec Nat n) → Nat
  foo zero    []       = 0
  foo (suc n) (x ∷ xs) = foo n xs

This is okay, since after matching on the length, the matching on the vector does not provide any computational information, and
any variables in the pattern (``x`` and ``xs`` in this case) are marked erased in turn.
On the other hand, if we don't match on the length first, the type checker complains:

.. code-block:: agda

  foo : (n : Nat) (@0 xs : Vec Nat n) → Nat
  foo n []       = 0
  foo n (x ∷ xs) = foo _ xs
  -- Error: Cannot branch on erased argument of datatype Vec Nat n

The type checker enters compile-time mode when

- checking a type, i.e. when moving to the right of a ``:``,
- checking erased arguments to a constructor or function, or
- checking the body of an erased definition

Note that the type checker does not enter compile-time mode based on the type a term is checked against. In particular
checking a term against ``Set`` does not trigger compile-time mode.



Subtyping of runtime-irrelevant function spaces
===============================================

Normally, if ``f : (@0 x : A) → B`` then we have ``λ x → f x : (x : A)
→ B`` but not ``f : (x : A) → B``.  When the option ``--subtyping`` is
enabled, Agda will make use of the subtyping rule ``(@0 x : A) → B <:
(x : A) → B``, so there is no need for eta-expanding the function
``f``.



.. _references:

References
==========

[1] Brady, Edwin, Conor McBride, and James McKinna. "Inductive Families Need Not Store Their Indices."
International Workshop on Types for Proofs and Programs. Springer, Berlin, Heidelberg, 2003.

[2] McBride, Conor. `"I Got Plenty o’Nuttin’." <https://personal.cis.strath.ac.uk/conor.mcbride/PlentyO-CR.pdf>`_
A List of Successes That Can Change the World. Springer, Cham, 2016.

[3] Atkey, Robert. `"The Syntax and Semantics of Quantitative Type Theory" <https://bentnib.org/quantitative-type-theory.html>`_.
In LICS '18: Oxford, United Kingdom. 2018.
