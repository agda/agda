
.. _rewriting:

*********
Rewriting
*********


Rewrite rules allow you to extend Agda's evaluation relation with new
computation rules.

Rules are safe to use with ```Agda.Builtin.Equality``
if :ref:`--confluence-check <confluence-check>` is enabled.
Confluent but non-terminating rewrite rules can not break consistency,
unlike to non-terminating functions.
Those results were proven by `Cockx, Tabareau, and Winterhalter <https://hal.science/hal-02901011v2/document>`_,
see section 3 for statements.

.. note:: This page is about the :option:`--rewriting` option and the
  associated :ref:`REWRITE <builtin-rewrite>` builtin. You might be
  looking for the documentation on the :ref:`rewrite construct
  <with-rewrite>` instead.

Rewrite rules by example
------------------------

To enable rewrite rules, you should run Agda with the flag :option:`--rewriting`
and import the modules ``Agda.Builtin.Equality`` and ``Agda.Builtin.Equality.Rewrite``:

::

  {-# OPTIONS --rewriting #-}

  module language.rewriting where

  open import Agda.Builtin.Equality
  open import Agda.Builtin.Equality.Rewrite

..
  ::

  open import Agda.Builtin.Nat
  variable
    A B C       : Set
    x y z       : A
    k l m n     : Nat

  cong : (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

  transport : (P : A → Set) → x ≡ y → P x → P y
  transport P refl p = p

Overlapping pattern matching
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To start, let's look at an example where rewrite rules can solve a
problem that is encountered by almost every newcomer to Agda.  This
problem usually pops up as the question why ``0 + m`` computes to
``m``, but ``m + 0`` does not (and similarly, ``(suc m) + n`` computes
to ``suc (m + n)`` but ``m + (suc n)`` does not). This problem
manifests itself for example when trying to prove commutativity of ``_+_``:

.. code-block:: agda

  +comm : m + n ≡ n + m
  +comm {m = zero}  = refl
  +comm {m = suc m} = cong suc (+comm {m = m})

Here, Agda complains that ``n != n + zero of type Nat``. The usual way
to solve this problem is by proving the equations ``m + 0 ≡ m`` and
``m + (suc n) ≡ suc (m + n)`` and using an explicit ``rewrite``
statement in the main proof (N.B.: Agda's ``rewrite`` keyword should not
be confused with rewrite rules, which are added by a ``REWRITE``
pragma.)

By using rewrite rules, we can simulate the solution from our
paper. First, we need to prove that the equations we want hold as
propositional equalities:

::

  +zero : m + zero ≡ m
  +zero {m = zero}  = refl
  +zero {m = suc m} = cong suc +zero

  +suc : m + (suc n) ≡ suc (m + n)
  +suc {m = zero}  = refl
  +suc {m = suc m} = cong suc +suc

Next we mark the equalities as rewrite rules with a ``REWRITE`` pragma:

::

  {-# REWRITE +zero +suc #-}

Now the proof of commutativity works exactly as we wrote it before:

::

  +comm : m + n ≡ n + m
  +comm {m = zero}  = refl
  +comm {m = suc m} = cong suc (+comm {m = m})


Note that there is no way to make this proof go through without
rewrite rules: it is essential that ``_+_`` computes both on its first
and its second argument, but there's no way to define ``_+_`` in such a
way using Agda's regular pattern matching.

More examples
~~~~~~~~~~~~~

Additional examples of how to use rewrite rules can be found in `a
blog post by Jesper Cockx
<https://jesper.sikanda.be/posts/hack-your-type-theory.html>`__.

General shape of rewrite rules
------------------------------

In general, an equality proof ``eq`` may be registered as a rewrite
rule using the pragma ``{-# REWRITE eq #-}``, provided the following
requirements are met:

* The type of ``eq`` is of the form ``eq : (x₁ : A₁) ... (xₖ : Aₖ) → f p₁ ... pₙ ≡ v``

* ``f`` is a postulate, a defined function symbol, or a constructor
  applied to fully general parameters (i.e. the parameters must be
  distinct variables)

* Each variable ``x₁``, ..., ``xₖ`` occurs at least once in a pattern
  position in ``p₁ ... pₙ`` (see below for the definition of pattern
  positions)

* The left-hand side ``f p₁ ... pₙ`` should be neutral, i.e. it should
  not reduce.

The following patterns are supported:

* ``x y₁ ... yₙ``, where ``x`` is a pattern variable and ``y₁``, ...,
  ``yₙ`` are distinct variables that are bound locally in the pattern

* ``f p₁ ... pₙ``, where ``f`` is a postulate, a defined function, a
  constructor, or a data/record type, and ``p₁``, ..., ``pₙ`` are
  again patterns

* ``λ x → p``, where ``p`` is again a pattern

* ``(x : P) → Q``, where ``P`` and ``Q`` are again patterns

* ``y p₁ ... pₙ``, where ``y`` is a variable bound locally in the
  pattern and ``p₁``, ..., ``pₙ`` are again patterns

* ``Set p`` or ``Prop p``, where ``p`` is again a pattern

* Any other term ``v`` (here the variables in ``v`` are not considered
  to be in a pattern position)

Once a rewrite rule has been added, Agda automatically rewrites all
instances of the left-hand side to the corresponding instance of the
right-hand side during reduction. More precisely, a term
(definitionally equal to) ``f p₁σ ... pₙσ`` is rewritten to ``vσ``,
where ``σ`` is any substitution on the pattern variables ``x₁``,
... ``xₖ``.

Since rewriting happens after normal reduction, rewrite rules are only
applied to terms that would otherwise be neutral.

.. _confluence-check:

Confluence checking
-------------------

Agda can optionally check confluence of rewrite rules by enabling the
:option:`--confluence-check` flag. Concretely, it does so by enforcing two
properties:

  1. For any two left-hand sides of the rewrite rules that overlap
     (either at the root position or at a subterm), the most general
     unifier of the two left-hand sides is again a left-hand side of a
     rewrite rule. For example, if there are two rules ``suc m + n =
     suc (m + n)`` and ``m + suc n = suc (m + n)``, then there should
     also be a rule ``suc m + suc n = suc (suc (m + n))``.

  2. Each rewrite rule should satisfy the *triangle property*: For any
     rewrite rule ``u = w`` and any single-step parallel unfolding ``u
     => v``, we should have another single-step parallel unfolding ``v
     => w``.

There is also a flag :option:`--local-confluence-check` that is less
restrictive but only checks local confluence of rewrite rules. In case
the rewrite rules are terminating (currently not checked), these two
properties are equivalent.

Advanced usage
--------------

Instead of importing ``Agda.Builtin.Equality.Rewrite``, a different
type may be chosen as the rewrite relation by registering it as the
``REWRITE`` builtin. For example, using the pragma ``{-# BUILTIN
REWRITE _~_ #-}`` registers the type ``_~_`` as the rewrite
relation. To qualify as the rewrite relation, the type must take at
least two arguments, and the final two arguments should be visible.
