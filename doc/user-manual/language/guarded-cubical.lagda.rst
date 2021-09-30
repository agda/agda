..
  ::

  {-# OPTIONS --cubical #-}
  module language.guarded-cubical where

.. _guarded-cubical:

********************
Guarded Cubical
********************

.. note::
   This is a stub.

Cubical Agda is extended with Nakano's later modality and guarded recursion based on Ticked Cubical Type Theory :ref:`[2] <cubical-refs>`.
For its usage, see :ref:`[1] <cubical-refs>` or the `example <https://github.com/agda/agda/blob/master/test/Succeed/LaterPrims.agda>`_.

The implementation currently allows for something more general than in the above reference, in
preparation for the ticks described in :ref:`[3] <cubical-refs>`.

Given a type `A` in the `primLockUniv` universe we can form function
types annotated with `@tick` (or its synonym `@lock`): `(@tick x : A)
-> B`.  Lambda abstraction at such a type introduces the variable in
the context with a `@tick` annotation. Application `t u` for
`t : (@tick x : A) → B` is restricted so that `t` is typable in the prefix
of the context that does not include any `@tick` variables in `u`. The
only exception to that restriction, at the moment, are variables of
interval `I`, or `IsOne _` type.


.. _cubical-refs:

References
==========

[1] Niccolò Veltri and Andrea Vezzosi. `"Formalizing pi-calculus in guarded cubical Agda." <https://doi.org/10.1145/3372885.3373814>`_
In CPP'20.  ACM, New York, NY, USA, 2020.

[2] Rasmus Ejlers Møgelberg and Niccolò Veltri. `"Bisimulation as path type for guarded recursive types." <https://doi.org/10.1145/3290317>`_ In POPL'19, 2019.

[3] Magnus Baunsgaard Kristensen, Rasmus Ejlers Møgelberg, Andrea Vezzosi. `"Greatest HITs: Higher inductive types in coinductive definitions via induction under clocks." <https://arxiv.org/abs/2102.01969>`_
