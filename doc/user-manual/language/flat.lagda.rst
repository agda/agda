..
  ::

  {-# OPTIONS --flat-split #-}

  module language.flat where

  open import Agda.Primitive
  open import Agda.Builtin.Equality

  variable
     A : Set
     B : Set
     P : A -> Set

.. _flat:

*************
Flat Modality
*************

The flat/crisp attribute ``@♭/@flat`` is an idempotent comonadic
modality modeled after `Spatial Type Theory
<https://arxiv.org/abs/1509.07584/>`_ and `Crisp Type Theory
<https://arxiv.org/abs/1801.07664/>`_. It is similar to a necessity modality.

This attribute is enabled using the infective flag :option:`--cohesion`.

We can define ``♭ A`` as a type for any ``(@♭ A : Set l)`` via an
inductive definition:

::

  data ♭ {@♭ l : Level} (@♭ A : Set l) : Set l where
    con : (@♭ x : A) → ♭ A

  counit : {@♭ l : Level} {@♭ A : Set l} → ♭ A → A
  counit (con x) = x


When trying to provide a ``@♭`` arguments only other ``@♭``
variables will be available, the others will be marked as ``@⊤`` in the context.
For example the following will not typecheck:

.. code-block:: agda

  unit : {@♭ l : Level} {@♭ A : Set l} → A → ♭ A
  unit x = con x

.. _pattern-matching-on-flat:

Pattern Matching on ``@♭``
----------------------------

By default matching on arguments marked with ``@♭`` is disallowed, but
it can be enabled using the option :option:`--flat-split`.
When matching on a ``@♭`` argument the flat
status gets propagated to the arguments of the constructor

::

  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  flat-sum : {@♭ A B : Set} → (@♭ x : A ⊎ B) → ♭ A ⊎ ♭ B
  flat-sum (inl x) = inl (con x)
  flat-sum (inr x) = inr (con x)


When refining ``@♭`` variables the equality also needs to be
provided as ``@♭``

::

  flat-subst : {@♭ A : Set} {P : A → Set} (@♭ x y : A) (@♭ eq : x ≡ y) → P x → P y
  flat-subst x .x refl p = p

if we simply had ``(eq : x ≡ y)`` the code would be rejected.

Note that in Cubical Agda functions that match on an argument marked
with ``@♭`` trigger the ``UnsupportedIndexedMatch`` warning (see
:ref:`indexed-inductive-types`), and the code might not compute
properly.


.. _sharp:

The Sharp Modality
----------------------------

The :option:`--cohesion` flag also enables the sharp modality as presented
in `Cohesive Homotopy Type Theory <https://arxiv.org/abs/1509.07584>`_.
The annotation ``@♯/@sharp`` is an idempotent monadic modality, which is
right adjoint to the ``@♭`` modality.

We can define ``♯`` as the following record type:

::

  record ♯ {l} (@♯ A : Set l) : Set l where
    constructor conSharp
    field
      @♯ ε : A

  open ♯

  _ : ∀ {@♭ l} {@♭ A : Set l} → @♭ ♯ A → A
  _ = ε

When providing a ``@♯`` argument, every non ``@⊤`` variable becomes
``@♭`` annotated. As a record, we can define elements of ``♯`` by
copattern matching. After copattern matching with ``ε``, all variables
in the context become crisp, for example, in the following, we can use
``a`` in the constuctor of ``♭``.

.. code-block:: agda

  unit : ∀ {@♭ A : Set} → A → ♯ (♭ A)
  unit a .ε = con a
