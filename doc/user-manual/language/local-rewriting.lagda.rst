
.. _local-rewriting:

***************
Local Rewriting
***************


Local rewrite rules is an experimental feature which enables parameterising
modules over computation rules. Specifically, it allows declaring
module parameters targetting a rewrite relation as local rewrite rules by
annotating with them the ``@rewrite`` attribute. Consequently:

* Inside the module, local rewrite rules will automatically apply during
  reduction, rewriting instances of the left-hand side to the right-hand side,
  similarly to :doc:`global rewriting <rewriting>`.
* Outside the module, local rewrite rules act as constraints on
  instantiations of the module parameters. E.g. when
  opening the module, Agda will check that both sides are
  definitionally equal.

This feature is based on Local Rewriting Type Theory (LRTT) as introduced in
`Encode the Cake and Eat It Too <https://hal.science/hal-05160846v1/document>`_,
by Yann Leray and Théo Winterhalter. Unlike their presentation, we do not
make a strong syntactic
distinction between the "interface environment" and the "local context", but
nonetheless, by restricting
``@rewrite`` attributes to module parameters, quantification over
rewrites is prenex-only. For example, definitions cannot return local rewrite
rules, or be parameterised over other definitions taking local rewrite rules,
so ``foo : (n : Nat) → ((@rewrite p : n ≡ 0) → Nat) → Nat`` is not allowed.

Semantically, local rewrite rules can
be eliminated by inlining all instantiations of modules with local rewrite
rule parameters and so should be conservative over the rest of
Agda's theory.

.. note:: This page is about the :option:`--local-rewriting` option. This is
  is unrelated to :option:`--local-confluence-check`, which enables a form of
  confluence checking for :doc:`global REWRITE rules <rewriting>` whilst using
  the :option:`--rewriting` option.

  It is also (currently) distinct from the the :ref:`rewrite construct
  <with-rewrite>`, although there are plans to implement a new version of
  :doc:`with-abstraction <with-abstraction>` which internally desugars to
  local rewrite rules ("smart with").

Local rewrite rules by example
------------------------------

::

  {-# OPTIONS --local-rewriting --rewriting #-}

  module language.local-rewriting where

  open import Agda.Builtin.Equality
  open import Agda.Builtin.Equality.Rewrite

..
  ::

  open import Agda.Builtin.Nat hiding (_+_)
  open import Agda.Builtin.Sigma
  open import Agda.Builtin.Unit
  open import Agda.Builtin.List

  _×_ : Set → Set → Set
  A × B = Σ A λ _ → B

  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  data ⊥ : Set where

  cong : ∀ {A B : Set} {x y} (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

  sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl q = q

To motivate local rewrite rules, consider the following code which implements
addition and proves associativity for Agda's built-in natural numbers.

::

  module Addition where
    _+_ : Nat → Nat → Nat
    zero  + m = m
    suc n + m = suc (n + m)

    +-assoc : ∀ {n m l} → (n + m) + l ≡ n + (m + l)
    +-assoc {n = zero}  = refl
    +-assoc {n = suc n} = cong suc (+-assoc {n = n})

Now imagine we want to use a different encoding of natural numbers - for
example, lists of unit values.

::

  Nat' = List ⊤

To define addition and prove associativity for ``Nat'`` without
duplication, we can parameterise our addition and the
associativity definitions over an abstract type of natural numbers and an
induction principle.

::

  module ParametricAddition
    (Nat : Set) (zero : Nat) (suc : Nat → Nat)
    (ind : (P : Nat → Set) → P zero → (∀ n → P n → P (suc n)) → ∀ n → P n)
    (ind-zero : ∀ {P z s} → ind P z s zero ≡ z)
    (ind-suc  : ∀ {P z s n} → ind P z s (suc n) ≡ s n (ind P z s n))
    where
    _+_ : Nat → Nat → Nat
    n + m = ind (λ _ → Nat) m (λ _ → suc) n

    +-assoc : ∀ {n m l} → (n + m) + l ≡ n + (m + l)
    +-assoc {n = n} {m = m} {l = l}
      = ind (λ □ → (□ + m) + l ≡ □ + (m + l))
            (trans (cong (_+ l) ind-zero) (sym ind-zero))
            (λ _ h → trans (cong (_+ l) ind-suc)
                   ( trans ind-suc
                   ( trans (cong suc h) (sym ind-suc))))
            n

We have succeeded in writing a single parametric definition of addition and
associativity, but at the cost of a much more convoluted proof.
The parameterised-over
induction principle no longer computes on zero and
successor automatically, so we have to manually invoke ``ind-zero`` and
``ind-suc`` multiple times.

Local rewrite rules resolve this tedium. We can simply annotate the ``ind-zero``
and ``ind-suc`` equations with ``@rewrite`` and recover the simple associativity
proof, whilst staying parametric over encoding details.

::

  module ParametricAdditionRew
    (Nat : Set) (zero : Nat) (suc : Nat → Nat)
    (ind : (P : Nat → Set) → P zero → (∀ n → P n → P (suc n)) → ∀ n → P n)
    (@rewrite ind-zero : ∀ {P z s} → ind P z s zero ≡ z)
    (@rewrite ind-suc  : ∀ {P z s n} → ind P z s (suc n) ≡ s n (ind P z s n))
    where
    _+_ : Nat → Nat → Nat
    n + m = ind (λ _ → Nat) m (λ _ → suc) n

    +-assoc : ∀ {n m l} → (n + m) + l ≡ n + (m + l)
    +-assoc {n = n} {m = m} {l = l}
      = ind (λ □ → (□ + m) + l ≡ □ + (m + l)) refl (λ _ h → cong suc h) n

For more examples on where local rewrite rules can be useful, see the
`Encode the Cake and Eat It Too <https://hal.science/hal-05160846v1/document>`_
paper.

Limitations
-----------

Confluence and termination checking
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Currently, no form of confluence or termination checking is implemented for
local rewrite rules. The consequences of non-confluent or non-terminating
local rewrite rules are similar to :doc:`global rewriting <rewriting>`:
non-confluence endangers subject reduction and non-termination might cause
the typechecker to loop, but logical soundness should never be threatened.

Refining local rewrite rules with pattern matching
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Currently, inaccessible pattern matches on variables that occur in local rewrite
rules are not allowed. This is to avoid typechecking under invalid rewrite rules
(rewrite validity is unstable under substitution).

.. code-block:: agda

  module _ (f : Nat → Nat) (@rewrite p : f 1 ≡ 0) where
    bad : f ≡ (λ x → x) → Nat
    bad refl = {!!} -- Substituting 'f' for 'λ x → x' here would invalidate the
                    -- local rewrite rule 'p'

Furthermore, matches on variables in local rewrite rules breaks the
inlining-based semantic justification.

In spite of these downsides, there are plans to relax this restriction in the
future under an additional flag. Refining local rewrite
rules with pattern matches enables a restricted form of
"local equality reflection", which has many interesting applications, including
a (hopefully) better-behaved :doc:`with-abstraction <with-abstraction>`
mechanism.

Parameterising datatypes over local rewrite rules with :option:`--cubical`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In :doc:`Cubical Agda <cubical>`, there is an additional limitation with local
rewrite rules. Attempting to declare data or record types inside modules with
local rewrite rule
parameters will throw a ``CannotGenerateTransportLocalRewrite`` error:

::

  module _ (n : Nat) (@rewrite _ : n ≡ 0) where
    data Foo : Set where
      mk : Foo

This restriction is due to how Cubical Agda automatically defines various
primitives
for datatypes for transport and path composition. It is not
(currently) clear what these should look like for datatypes with local
rewrite rule parameters.

If you run into this issue, try defining your data or record
types outside of the module with the local rewrite rule.
