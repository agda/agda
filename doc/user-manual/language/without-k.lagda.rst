..
  ::
  module language.without-k where

.. _without-k:

*********
Without K
*********

.. versionadded:: 2.2.10

The option ``--without-K`` makes pattern matching more restricted. If
the option is activated, then Agda only accepts certain case-splits.

.. versionchanged:: 2.3.2

If the type of the variable to be split is ``D pars ixs``, where ``D``
is a data (or record) type, ``pars`` stands for the parameters, and
``ixs`` the indices, then the following requirements must be
satisfied:

  * The indices ``ixs`` must be applications of constructors (or
    literals) to distinct variables. Constructors are usually not
    applied to parameters, but for the purposes of this check
    constructor parameters are treated as other arguments.

  * These distinct variables must not be free in pars.

The intended purpose of ``--without-K`` is to enable experiments with
a propositional equality without the K rule. Let us define
propositional equality as follows::

  data _≡_ {A : Set} : A → A → Set where
    refl : ∀ x → x ≡ x

Then the obvious implementation of the J rule is accepted::

  J : {A : Set} (P : {x y : A} → x ≡ y → Set) →
      (∀ x → P (refl x)) →
      ∀ {x y} (x≡y : x ≡ y) → P x≡y
  J P p (refl x) = p x

The same applies to Christine Paulin-Mohring's version of the J rule::

  J′ : {A : Set} {x : A} (P : {y : A} → x ≡ y → Set) →
       P (refl x) →
       ∀ {y} (x≡y : x ≡ y) → P x≡y
  J′ P p (refl x) = p

On the other hand, the obvious implementation of the K rule is not
accepted::

  K : {A : Set} (P : {x : A} → x ≡ x → Set) →
      (∀ x → P (refl x)) →
      ∀ {x} (x≡x : x ≡ x) → P x≡x
  K P p (refl x) = p x

However, we have *not* proved that activation of ``--without-K``
ensures that the K rule cannot be proved in some other way.

.. versionadded:: 2.4.2

The option ``--with-K`` can be used to override a global
``--without-K`` in a file, by adding a pragma
``{-# OPTIONS --with-K #-}``. This option is on by default.
