..
  ::
  {-# OPTIONS --polarity #-}

  module language.polarity where

  open import Agda.Builtin.Nat

.. _polarity:

======================
 Polarity Annotations
======================

Agda supports explicitly annotating functions arguments and datatype parameters
with their polarities, using a :ref:`modality system <modalities>`, which the
positivity checker can then use to infer positivity. This experimental feature
has to be enabled by the :option:`--polarity` option. Here are some sample uses
of the different annotations which type-check: ::

  strictly-positive : @++ Set → Set
  strictly-positive A = Nat → A

  positive : @+ Set → Set
  positive A = (A → Nat) → A

  negative : @- Set → Set
  negative A = A → Nat

  mixed : @mixed Set → Set
  mixed A = A → A

  unused : @unused Set → Set
  unused A = Nat

  ex : @- Set → Set
  ex A = negative (positive A)

  ex2 : @mixed Set → Set
  ex2 A = mixed (strictly-positive A)

  ex3 : @++ Set → Set
  ex3 A = unused (negative A)

The following code doesn't type-check:

.. code-block:: agda

  ex3 : @++ Set → Set
  ex3 A = mixed (strictly-positive A)

The standard use-case is defining the fix-point of any strictly positive
type-former (which is already the criterion for an inductive type to be
definable in Agda, see :ref:`strict-positivity`, but the polarity modality
internalizes this criterion into the type system): ::

  data Mu (F : @++ Set → Set) : Set where
    fix : F (Mu F) → Mu F

In the example above, because ``F`` is specified as using its argument strictly
positively, the positivity checker allows ``F (Mu F)`` as an argument to a
constructor since it knows the recursive call to ``Mu F`` is in strictly
positive position.

When defining functions that take arguments annotated with ``@++``, the typing
rules ensure that those arguments may never actually appear to the left of an
arrow. They can syntactically appear to the left of an arrow as arguments to
functions that don't use their arguments, such as in the correct example below:
::

  const : @unused Set → Set
  const _ = Nat

  typechecks : @++ Set → Set
  typechecks A = const A → Nat

The polarity modality
=====================

Agda implements polarity annotations using a modal system. Here are the
different modalities and their meaning:

+--------+-------------------+-------------------------------------+
|Notation|Name               |Possible use                         |
+========+===================+=====================================+
|@++     |Strictly positive  |Anywhere except in the domain of a   |
|        |                   |pi/function type                     |
+--------+-------------------+-------------------------------------+
|@+      |Positive           |In an even number of nested domains  |
|        |                   |of pi/function types                 |
+--------+-------------------+-------------------------------------+
|@-      |Negative           |In an odd number of nested domains of|
|        |                   |pi/function types                    |
+--------+-------------------+-------------------------------------+
|@mixed  |Mixed              |Anywhere                             |
+--------+-------------------+-------------------------------------+
|@unused |Unused             |Nowhere                              |
+--------+-------------------+-------------------------------------+

Strictly positive types are a syntactical condition described for example in
section 2.3 of :ref:`[1] <polarity-refs>`. A very similar system (without strict
positivity) was described in :ref:`[2] <polarity-refs>`, but didn't use the
modality formalism.

When Agda type-checks any definition, it ensures that the variables bound by a
lambda-abstraction with annotated types satisfy those restrictions.  Note that
there is no such restriction when checking the codomain of a pi type, so for
example ``(@++ A : Set) → (A → A)`` is perfectly valid!

Polarity annotations can only appear on domains of function types and
data/record type parameters. Pattern-matching on annotated arguments is only
supported for mixed arguments.

Positivity checking
===================

The Agda positivity checker uses the polarity annotations in the typing
information to enhance its analysis and accept types like ``Mu`` above. This can
also help when the positivity checker is unable to automatically infer that
information itself. Here is a contrived example that doesn't type-check without
annotations: ::

  apply-pattern-match : {A B : Set₁} → Nat → (@++ A → B) → @++ A → B
  apply-pattern-match zero f = f
  apply-pattern-match (suc n) f = f

  id : {A : Set₁} → @++ A → A
  id x = x

  data D : Set where
    node : (u : Nat) → apply-pattern-match u id D → D

.. _polarity-refs:

References
==========

[1] Michael Abbott, Thorsten Altenkirch, Neil Ghani,
"Containers: Constructing strictly positive types",
In Theoretical Computer Science,
Volume 342, Issue 1,
2005,
https://doi.org/10.1016/j.tcs.2005.06.002

[2] Andreas Abel, "Polarized Subtyping for Sized Types", In: Mathematical
Structures in Computer Science, 2006, https://doi.org/10.1007/11753728_39
