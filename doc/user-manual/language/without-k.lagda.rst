..
  ::
  module language.without-k where
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Coinduction

.. _without-k:

*********
Without K
*********

The option ``--without-K`` makes pattern matching more restricted. If
the option is activated, then Agda only accepts certain case
splits. This option was added in Agda 2.2.10.

Since Agda 2.4.0 when the option ``--without-K`` is enabled, then the
unification algorithm for checking case splits cannot make use of the
deletion rule to solve equations of the form ``x = x``.

For example, the obvious implementation of the J rule is accepted::

  J : {A : Set} (P : (x y : A) → x ≡ y → Set) →
      ((x : A) → P x x refl) → (x y : A) (x≡y : x ≡ y) → P x y x≡y
  J P p x .x refl = p x

Pattern matching with the constructor ``refl`` on the argument ``x≡y``
causes ``x`` to be unified with ``y``. The same applies to Christine
Paulin-Mohring's version of the J rule::

  J′ : {A : Set} {x : A} (P : (y : A) → x ≡ y → Set) →
       P x refl → (y : A) (x≡y : x ≡ y) → P y x≡y
  J′ P p ._ refl = p

On the other hand, the obvious implementation of the K rule is not
accepted::

  K : {A : Set} {x : A} (P : x ≡ x → Set) →
      P refl → (x≡x : x ≡ x) → P x≡x
  K P p refl = p

Pattern matching with the constructor ``refl`` on the argument ``x≡x``
causes ``x`` to be unified with ``x``, which fails because the deletion
rule cannot be used when ``--without-K`` is enabled.

For more details, see the paper `Eliminating dependent pattern matching
without K` [`Cockx, Devriese, and Piessens (2016) <https://lirias.kuleuven.be/handle/123456789/548901/>`_].

The option ``--with-K`` can be used to override a global
``--without-K`` in a file, by adding a pragma
``{-# OPTIONS --with-K #-}``. This option was added in Agda 2.4.2 and
it is on by default.

Since Agda 2.4.2 termination checking ``--without-K`` restricts
structural descent to arguments ending in data types or ``Size``.
Likewise, guardedness is only tracked when result type is data or
record type::

  data ⊥ : Set where

  mutual
    data WOne : Set where wrap : FOne → WOne
    FOne = ⊥ → WOne

  postulate iso : WOne ≡ FOne

  noo : (X : Set) → (WOne ≡ X) → X → ⊥
  noo .WOne refl (wrap f) = noo FOne iso f

``noo`` is rejected since at type ``X`` the structural descent
``f < wrap f`` is discounted ``--without-K``::

  data Pandora : Set where
    C : ∞ ⊥ → Pandora

  postulate foo : ⊥ ≡ Pandora

  loop : (A : Set) → A ≡ Pandora → A
  loop .Pandora refl = C (♯ (loop ⊥ foo))

``loop`` is rejected since guardedness is not tracked at type ``A``
``--without-K``.

See issues `#1023 <https://github.com/agda/agda/issues/1023/>`_,
`#1264 <https://github.com/agda/agda/issues/1264/>`_,
`#1292 <https://github.com/agda/agda/issues/1292/>`_.
