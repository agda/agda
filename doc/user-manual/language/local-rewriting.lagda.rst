
.. _local-rewriting:

***************
Local Rewriting
***************


Local rewrite rules is an experimental feature which enables parameterising
developments over computation rules. Specifically, it allows declaring
module parameters targetting a rewrite relation as local rewrite rules by
annotating with them the ``@rew`` attribute. Consequently:

* Inside the module, local rewrite rules will automatically apply during
  reduction, rewriting instances of the left-hand side with the right-hand side,
  similarly to :doc:`global rewriting <rewriting>`.
* Outside the module, local rewrite rules act as constraints. E.g. when
  opening the module, Agda will check that both sides are
  definitionally equal.

This feature is based on Local Rewriting Type Theory (LRTT) as presented in
`Encode the Cake and Eat It Too <https://hal.science/hal-05160846v1/document>`_,
by Yann Leray and Théo Winterhalter. We do not make as strong a syntactic
distinction between the interface and the local context, but by restricting
``@rew`` annotations to module parameters, we maintain the key restriction
that quantification over local rewrite rules is prenex-only.
Semantically, local rewrite rules can
be eliminated with inlining and so should be conservative over the rest of
Agda's theory.

.. note:: This page is about the :option:`--local-rewriting` option. This is
  is unrelated to :option:`--local-confluence-check`, which confluence
  checks :doc:`global rewrite rules <rewriting>` while using the
  :option:`--rewriting` option.

  It is also (currently) distinct from the the :ref:`rewrite construct
  <with-rewrite>`, although there are plans to implement a new version of
  :doc:`with-abstraction <with-abstraction>` by desugaring to the local
  rewrite rules described here.

Local rewrite rules by example
------------------------------

::

  {-# OPTIONS --local-rewriting #-}

  module language.local-rewriting where

  open import Agda.Builtin.Equality
  open import Agda.Builtin.Equality.Rewrite

..
  ::

  open import Agda.Builtin.Nat


TODO

For more examples on where local rewrite rules can be useful, see the
`Encode the Cake and Eat It Too <https://hal.science/hal-05160846v1/document>`_
paper.

Limitations
-----------

Confluence and termination checking
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Currently, no form of confluence of termination checking is implemented for
local rewrite rules. The consequences of non-confluent or non-terminating
local rewrite rules are similar to :doc:`global rewriting <rewriting>`:
non-confluence endangers subject reduction and non-termination might cause
the typechecker to loop.

Refining local rewrite rules with pattern matching
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Currently, forced pattern matches on variables that occur in local rewrite rules
are not allowed. This is to avoid typechecking under invalid rewrite rules
(rewrite validity is unstable under substitution).

.. code-block:: agda

  module _ (f : Nat → Nat) (@rew p : f 1 ≡ 0) where
    bad : f ≡ (λ x → x) → Nat
    bad refl = {!!} -- Substituting 'f' for 'λ x → x' here would invalidate the
                    -- local rewrite rule 'p'

Furthermore, matches on variables in local rewrite rules breaks the
inlining-based semantic justification.

In spite of these downsides, there are plans to relax this restriction in the
future under
an even more experimental flag. It turns out allowing refining local rewrite
rules with pattern matches enables a restricted form of
`local equality reflection', which has many interesting applications, including
a (hopefully) better-behaved :doc:`with-abstraction <with-abstraction>`
mechanism.

Parameterising datatypes over local rewrite rules with :option:`--cubical`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In :doc:`Cubical Agda <cubical>`, there an additional limitation with local
rewrite rules. Attempting to declare data or record types inside modules with
local rewrite rule
parameters will throw a ``CannotGenerateTransportLocalRewrite`` error:

::

  module _ (n : Nat) (@rew _ : n ≡ 0) where
    data Foo : Set where
      mk : Foo

The problem related to how Cubical Agda automatically defines various primitives
for datatypes for transport and path composition. It is not
(currently) clear what these should look like for datatypes with local
rewrite rule parameters.

If you run into this issue, try defining your data or record
types outside of the module with the local rewrite rule.
