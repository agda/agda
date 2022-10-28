..
  ::
  {-# OPTIONS --guardedness #-}

  module language.without-k where
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Coinduction

.. _without-k:

*********
Without K
*********


The option :option:`--without-K` adds some restrictions to Agda's
typechecking algorithm in order to ensure compatability with versions of
type theory that do not support UIP (uniqueness of identity proofs),
such as HoTT (homotopy type theory).

The option :option:`--with-K` can be used to override a global
:option:`--without-K` in a file, by adding a pragma
``{-# OPTIONS --with-K #-}``. This option is enabled by default.

.. note::
  Prior to Agda 2.6.3, the :option:`--cubical-compatible` flag did not exist,
  and :option:`--without-K` also implied the (internal) generation of Cubical
  Agda-specific code. See :ref:`cubical-compatible` for the specifics,
  and `#5843 <https://github.com/agda/agda/issues/5843>` for the
  rationale.

.. note::
   When `--without-K` is used, it is not safe to postulate erased
   univalence: the theory is perhaps consistent, but one can get
   incorrect results at run-time. You should use the
   :ref:`cubical-compatible` flag instead. See `#4784
   <https://github.com/agda/agda/issues/4784>` for more details on
   this restriction.

Restrictions on pattern matching
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When the option :option:`--without-K` is enabled, then Agda only accepts
certain case splits. More specifically, the unification algorithm for
checking case splits cannot make use of the deletion rule to solve
equations of the form ``x = x``.

For example, the obvious implementation of the K rule is not
accepted::

  K : {A : Set} {x : A} (P : x ≡ x → Set) →
      P refl → (x≡x : x ≡ x) → P x≡x
  K P p refl = p

Pattern matching with the constructor ``refl`` on the argument ``x≡x``
causes ``x`` to be unified with ``x``, which fails because the deletion
rule cannot be used when :option:`--without-K` is enabled.

On the other hand, the obvious implementation of the J rule is accepted::

  J : {A : Set} (P : (x y : A) → x ≡ y → Set) →
      ((x : A) → P x x refl) → (x y : A) (x≡y : x ≡ y) → P x y x≡y
  J P p x .x refl = p x

Pattern matching with the constructor ``refl`` on the argument ``x≡y``
causes ``x`` to be unified with ``y``. The same applies to Christine
Paulin-Mohring's version of the J rule::

  J′ : {A : Set} {x : A} (P : (y : A) → x ≡ y → Set) →
       P x refl → (y : A) (x≡y : x ≡ y) → P y x≡y
  J′ P p ._ refl = p

For more details, see Jesper Cockx's PhD thesis `Dependent Pattern
Matching and Proof-Relevant Unification` [`Cockx (2017)
<https://limo.libis.be/primo-explore/fulldisplay?docid=LIRIAS1656778&context=L&vid=Lirias>`_].

Restrictions on termination checking
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When :option:`--without-K` is enabled, Agda's termination checker restricts
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
``f < wrap f`` is discounted :option:`--without-K`::

  data Pandora : Set where
    C : ∞ ⊥ → Pandora

  postulate foo : ⊥ ≡ Pandora

  loop : (A : Set) → A ≡ Pandora → A
  loop .Pandora refl = C (♯ (loop ⊥ foo))

``loop`` is rejected since guardedness is not tracked at type ``A``
:option:`--without-K`.

See issues `#1023 <https://github.com/agda/agda/issues/1023/>`_,
`#1264 <https://github.com/agda/agda/issues/1264/>`_,
`#1292 <https://github.com/agda/agda/issues/1292/>`_.

Restrictions on universe levels
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When :option:`--without-K` is enabled, some indexed datatypes must be
defined in a higher universe level. In particular, the types of all
indices should fit in the sort of the datatype.

For example, usually (i.e. :option:`--with-K`) Agda allows the following
definition of equality::

  data _≡₀_ {ℓ} {A : Set ℓ} (x : A) : A → Set where
    refl : x ≡₀ x

However, with :option:`--without-K` it must be defined at a higher
universe level::

  data _≡′_ {ℓ} {A : Set ℓ} : A → A → Set ℓ where
    refl : {x : A} → x ≡′ x
