..
  ::
  module language.postulates where

.. _postulates:

**********
Postulates
**********

A postulate is a declaration of an element of some type without an accompanying definition. With postulates we can introduce elements in a type without actually giving the definition of the element itself.

The general form of a postulate declaration is as follows:

.. code-block:: agda

  postulate
      c11 ... c1i : <Type>
      ...
      cn1 ... cnj : <Type>

Example: ::

  postulate
    A B    : Set
    a      : A
    b      : B
    _=AB=_ : A → B → Set
    a==b   : a =AB= b

Introducing postulates is in general not recommended. Once postulates are introduced the consistency of the whole development is at risk, because there is nothing that prevents us from introducing an element in the empty set.

::

  data False : Set where

  postulate bottom : False

Postulates are forbidden in :ref:`Safe Agda <safe-agda>` (option :option:`--safe`) to prevent accidential inconsistencies.

A preferable way to work with assumptions is to define a module parametrised by the elements we need::

  module Absurd (bt : False) where

    -- ...

  module M (A B : Set) (a : A) (b : B)
           (_=AB=_ : A → B → Set) (a==b : a =AB= b) where

    -- ...


Postulated built-ins
--------------------

Some :ref:`built-ins <built-ins>` such as `Float` and `Char` are introduced as a postulate and then given a meaning by the corresponding ``{-# BUILTIN ... #-}`` pragma.

Local uses of ``postulate``
---------------------------

Postulates are declarations and can appear in positions where arbitrary declarations are allowed, e.g., in ``where`` blocks::

  module PostulateInWhere where

    my-theorem : (A : Set) → A
    my-theorem A = I-prove-this-later
      where
        postulate I-prove-this-later : _
