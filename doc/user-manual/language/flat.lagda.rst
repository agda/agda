..
  ::

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

Agda allows matching on ``@♭`` arguments by default.
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

Pattern matching on ``@♭`` arguments can be disabled entirely by using
the ``--no-flat-split`` flag

.. code-block:: agda

  {-# OPTIONS --no-flat-split #-}
