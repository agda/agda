..
  ::

  {-# OPTIONS --cubical #-}
  {-# OPTIONS -WnoUnsupportedIndexedMatch #-} -- silence warnings for indexed families

  module language.cubical where

  open import Agda.Primitive
  open import Agda.Primitive.Cubical
    renaming ( primIMin to _∧_
             ; primIMax to _∨_
             ; primINeg to ~_
             ; primHComp to hcomp
             ; primTransp to transp
             ; itIsOne to 1=1 )
  open import Agda.Builtin.Cubical.Path
  open import Agda.Builtin.Cubical.Sub
    renaming ( primSubOut to outS )
  open import Agda.Builtin.Cubical.Glue public
    using ( isEquiv
          ; equiv-proof
          ; _≃_
          ; primGlue )
  open import Agda.Builtin.Cubical.Id public
    using ( Id
          ; conid
          ; primIdElim
          ; reflId
          )

  open import Agda.Builtin.Sigma public
  open import Agda.Builtin.Bool public
  open import Agda.Builtin.Nat public

  infix 2 Σ-syntax

  Σ-syntax : ∀ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') → Set (ℓ ⊔ ℓ')
  Σ-syntax = Σ

  syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

  _×_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
  A × B = Σ A (λ _ → B)

  infixr 5 _×_

  -- This proof is hidden up here because its definition isn't relevant
  -- to the docs. But we do need its existence.
  transport⁻Transport : ∀ {ℓ} {A B : Set ℓ} (p : A ≡ B) (a : A)
                      → transp (λ i → p (~ i)) i0 (transp (λ i → p i) i0 a) ≡ a
  transport⁻Transport p a i =
    transp (λ j → p (~ i ∧ ~ j)) i (transp (λ j → p (~ i ∧ j)) i a)

.. _cubical:

*******
Cubical
*******

The Cubical mode extends Agda with a variety of features from Cubical
Type Theory. In particular, computational univalence and higher
inductive types which hence gives computational meaning to `Homotopy
Type Theory and Univalent Foundations
<https://homotopytypetheory.org/>`_. The version of Cubical Type
Theory that Agda implements is a variation of the `CCHM`_ Cubical Type
Theory where the Kan composition operations are decomposed into
homogeneous composition and generalized transport. This is what makes
the general schema for higher inductive types work, following the
`CHM`_ paper.

To use the cubical mode Agda needs to be run with the
:option:`--cubical` command-line-option or with ``{-#
OPTIONS --cubical #-}`` at the top of the file. There is also a
variant of the cubical mode, activated using
:option:`--erased-cubical`, which is described
:ref:`below<erased-cubical>`.

The cubical mode adds the following features to Agda:

1. An interval type and path types
2. Generalized transport (``transp``)
3. Partial elements
4. Homogeneous composition (``hcomp``)
5. Glue types
6. Higher inductive types
7. Cubical identity types

There is a standard ``agda/cubical`` library for Cubical Agda
available at https://github.com/agda/cubical. This documentation uses
the naming conventions of this library, for a detailed list of all of
the built-in Cubical Agda files and primitives see
:ref:`primitives-ref`. The main design choices of the core part of the
library are explained in
https://homotopytypetheory.org/2018/12/06/cubical-agda/
(lagda rendered version:
https://ice1000.org/2018/12-06-CubicalAgda.html).

The recommended way to get access to the Cubical primitives is to add
the following to the top of a file (this assumes that the
``agda/cubical`` library is installed and visible to Agda).

.. code-block:: agda

  {-# OPTIONS --cubical #-}

  open import Cubical.Core.Everything

For detailed install instructions for ``agda/cubical`` see:
https://github.com/agda/cubical/blob/master/INSTALL.md. In order to
make this library visible to Agda add
``/path/to/cubical/cubical.agda-lib`` to ``.agda/libraries`` and
``cubical`` to ``.agda/defaults`` (where ``path/to`` is the absolute
path to where the ``agda/cubical`` library has been installed). For
details of Agda's library management see :ref:`package-system`.

Expert users who do not want to rely on ``agda/cubical`` can just add
the relevant import statements at the top of their file (for details
see :ref:`primitives-ref`). However, for beginners it is
recommended that one uses at least the core part of the
``agda/cubical`` library.

There is also an older version of the library available at
https://github.com/Saizan/cubical-demo/. However this is relying on
deprecated features and is not recommended to use.

The interval and path types
===========================

The key idea of Cubical Type Theory is to add an interval type ``I :
IUniv`` (the reason this is in a special sort ``IUniv`` is because it
doesn't support the ``transp`` and ``hcomp`` operations). A variable
``i : I`` intuitively corresponds to a point in the `real unit interval
<https://en.wikipedia.org/wiki/Unit_interval>`_. In an empty context,
there are only two values of type ``I``: the two endpoints of the
interval, ``i0`` and ``i1``.

.. code-block:: agda

  i0 : I
  i1 : I

Elements of the interval form a `De Morgan algebra
<https://en.wikipedia.org/wiki/De_Morgan_algebra>`_, with minimum
(``∧``), maximum (``∨``) and negation (``~``).

.. code-block:: agda

  _∧_ : I → I → I
  _∨_ : I → I → I
  ~_ : I → I

All the properties of De Morgan algebras hold definitionally. The
endpoints of the interval ``i0`` and ``i1`` are the bottom and top
elements, respectively.

.. code-block:: agda

    i0 ∨ i    = i
    i  ∨ i1   = i1
    i  ∨ j    = j ∨ i
    i0 ∧ i    = i0
    i1 ∧ i    = i
    i  ∧ j    = j ∧ i
    ~ (~ i)   = i
    i0        = ~ i1
    ~ (i ∨ j) = ~ i ∧ ~ j
    ~ (i ∧ j) = ~ i ∨ ~ j

The core idea of Homotopy Type Theory and Univalent Foundations is a
correspondence between paths (as in topology) and (proof-relevant)
equalities (as in Martin-Löf's identity type). This correspondence is
taken very literally in Cubical Agda where a path in a type ``A`` is
represented like a function out of the interval, ``I → A``. A
path type is in fact a special case of the more general built-in
heterogeneous path types:

::

  -- PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

  -- Non dependent path types
  Path : ∀ {ℓ} (A : Set ℓ) → A → A → Set ℓ
  Path A a b = PathP (λ _ → A) a b

The central notion of equality in Cubical Agda is hence heterogeneous
equality (in the sense of ``PathOver`` in HoTT). To define paths we
use λ-abstractions and to apply them we use regular application.  For
example, this is the definition of the constant path (or proof of
reflexivity):

::

  refl : ∀ {ℓ} {A : Set ℓ} {x : A} → Path A x x
  refl {x = x} = λ i → x

Although they use the same syntax, a path is not exactly the same as a
function. For example, the following is not valid:

.. code-block:: agda

  refl : ∀ {ℓ} {A : Set ℓ} {x : A} → Path A x x
  refl {x = x} = λ (i : I) → x

Because of the intuition that paths correspond to equality ``PathP (λ
i → A) x y`` gets printed as ``x ≡ y`` when ``A`` does not mention
``i``. By iterating the path type we can define squares, cubes, and
higher cubes in Agda, making the type theory cubical. For example a
square in ``A`` is built out of 4 points and 4 lines:

::

  Square : ∀ {ℓ} {A : Set ℓ} {x0 x1 y0 y1 : A} →
             x0 ≡ x1 → y0 ≡ y1 → x0 ≡ y0 → x1 ≡ y1 → Set ℓ
  Square p q r s = PathP (λ i → p i ≡ q i) r s

Viewing equalities as functions out of the interval makes it possible
to do a lot of equality reasoning in a very direct way:

::

  sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
  sym p = λ i → p (~ i)

  cong : ∀ {ℓ} {A : Set ℓ} {x y : A} {B : A → Set ℓ} (f : (a : A) → B a) (p : x ≡ y)
         → PathP (λ i → B (p i)) (f x) (f y)
  cong f p i = f (p i)

Because of the way functions compute these satisfy some new
definitional equalities compared to the standard Agda definitions:

::

  symInv : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → sym (sym p) ≡ p
  symInv p = refl

  congId : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → cong (λ a → a) p ≡ p
  congId p = refl

  congComp : ∀ {ℓ} {A B C : Set ℓ} (f : A → B) (g : B → C) {x y : A} (p : x ≡ y) →
               cong (λ a → g (f a)) p ≡ cong g (cong f p)
  congComp f g p = refl

Path types also lets us prove new things are not provable in standard
Agda, for example function extensionality (pointwise equal functions
are equal) has an extremely simple proof:

::

  funExt : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x} →
             ((x : A) → f x ≡ g x) → f ≡ g
  funExt p i x = p x i

Transport
=========

While path types are great for reasoning about equality they don't let
us transport along paths between types or even compose paths, which in
particular means that we cannot yet prove the induction principle for
paths. In order to remedy this we also have a built-in (generalized)
transport operation `transp` and homogeneous composition operations `hcomp`. The
transport operation is generalized in the sense that it lets us
specify where it is the identity function.

.. code-block:: agda

  transp : ∀ {ℓ} (A : I → Set ℓ) (r : I) (a : A i0) → A i1

There is an additional side condition to be satisfied for a usage of ``transp`` to type-check: ``A`` should be a constant function whenever the constraint ``r = i1`` is satisfied. By constant here we mean that ``A`` is definitionally equal to ``λ _ → A i0``, which in turn requires ``A i0`` and ``A i1`` to be definitionally equal as well.

When ``r`` is ``i1``, ``transp A r`` will compute as the identity function.

.. code-block:: agda

   transp A i1 a = a

This is only sound if in such a case ``A`` is a trivial path, as the side condition requires.

It might seems strange that the side condition expects ``r`` and
``A`` to interact, but both of them can depend on any of the
interval variables in scope, so assuming a specific value for ``r``
can affect what ``A`` looks like.

Some examples of the side condition for different values of ``r``:

* If ``r`` is some in-scope variable ``i``, on which ``A`` may depend as well, then ``A`` only needs to be
  a constant function when substituting ``i1`` for ``i``.

* If ``r`` is ``i0`` then there is no restrition on ``A``, since the side
  condition is vacuously true.

* If ``r`` is ``i1`` then ``A`` must be a constant function.


We can use ``transp`` to define regular transport:

::

  transport : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
  transport p a = transp (λ i → p i) i0 a

By combining the transport and min operations we can define the
induction principle for paths:

::

  J : ∀ {ℓ} {A : Set ℓ} {x : A} (P : ∀ y → x ≡ y → Set ℓ)
        (d : P x refl) {y : A} (p : x ≡ y)
      → P y p
  J P d p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

One subtle difference between paths and the propositional equality
type of Agda is that the computation rule for ``J`` does not hold
definitionally. If ``J`` is defined using pattern-matching as in the
Agda standard library then this holds, however as the path types are
not inductively defined this does not hold for the above definition of
``J``. In particular, transport in a constant family is only the
identity function up to a path which implies that the computation rule
for ``J`` only holds up to a path:

::

  transportRefl : ∀ {ℓ} {A : Set ℓ} (x : A) → transport refl x ≡ x
  transportRefl {A = A} x i = transp (λ _ → A) i x

  JRefl : ∀ {ℓ} {A : Set ℓ} {x : A} (P : ∀ y → x ≡ y → Set ℓ)
           (d : P x refl) → J P d refl ≡ d
  JRefl P d = transportRefl d

Internally in Agda the ``transp`` operation computes by cases on the
type, so for example for Σ-types it is computed elementwise. For path
types it is however not yet possible to provide the computation rule
as we need some way to remember the endpoints of the path after
transporting it. Furthermore, this must work for arbitrary higher
dimensional cubes (as we can iterate the path types). For this we
introduce the "homogeneous composition operations" (``hcomp``) that
generalize binary composition of paths to n-ary composition of higher
dimensional cubes.


Partial elements
================

In order to describe the homogeneous composition operations we need to
be able to write partially specified n-dimensional cubes (i.e. cubes
where some faces are missing). Given an element of the interval ``r :
I`` there is a predicate ``IsOne`` which represents the constraint ``r
= i1``. This comes with a proof that ``i1`` is in fact equal to ``i1``
called ``1=1 : IsOne i1``. We use Greek letters like ``φ`` or ``ψ``
when such an ``r`` should be thought of as being in the domain of
``IsOne``.

Using this we introduce a type of partial elements called ``Partial φ
A``, this is a special version of ``IsOne φ → A`` with a more
extensional judgmental equality (two elements of ``Partial φ A`` are
considered equal if they represent the same subcube, so the faces of
the cubes can for example be given in different order and the two
elements will still be considered the same). The idea is that
``Partial φ A`` is the type of cubes in ``A`` that are only defined
when ``IsOne φ``.  There is also a dependent version of this called
``PartialP φ A`` which allows ``A`` to be defined only when ``IsOne
φ``.

.. code-block:: agda

  Partial : ∀ {ℓ} → I → Set ℓ → SSet ℓ

  PartialP : ∀ {ℓ} → (φ : I) → Partial φ (Set ℓ) → SSet ℓ

There is a new form of pattern matching that can be used to introduce partial elements:

::

  partialBool : ∀ i → Partial (i ∨ ~ i) Bool
  partialBool i (i = i0) = true
  partialBool i (i = i1) = false

The term ``partialBool i`` should be thought of a boolean with different
values when ``(i = i0)`` and ``(i = i1)``. Terms of type ``Partial φ
A`` can also be introduced using a :ref:`pattern-lambda`.

::

  partialBool' : ∀ i → Partial (i ∨ ~ i) Bool
  partialBool' i = λ { (i = i0) → true
                     ; (i = i1) → false }

When the cases overlap they must agree (note that the order of the
cases doesn't have to match the interval formula exactly):

::

  partialBool'' : ∀ i j → Partial (~ i ∨ i ∨ (i ∧ j)) Bool
  partialBool'' i j = λ { (i = i1)          → true
                        ; (i = i1) (j = i1) → true
                        ; (i = i0)          → false }

Furthermore ``IsOne i0`` is actually absurd.

::

  empty : {A : Set} → Partial i0 A
  empty = λ { () }

Cubical Agda also has cubical subtypes as in the CCHM type theory:

::

  _[_↦_] : ∀ {ℓ} (A : Set ℓ) (φ : I) (u : Partial φ A) → SSet ℓ
  A [ φ ↦ u ] = Sub A φ u

A term ``v : A [ φ ↦ u ]`` should be thought of as a term of type
``A`` which is definitionally equal to ``u : A`` when ``IsOne φ`` is
satisfied. Any term ``u : A`` can be seen as an term of ``A [ φ ↦ u
]`` which agrees with itself on ``φ``:

.. code-block:: agda

  inS : ∀ {ℓ} {A : Set ℓ} {φ : I} (u : A) → A [ φ ↦ (λ _ → u) ]

One can also forget that a partial element agrees with ``u`` on ``φ``:

.. code-block:: agda

  outS : ∀ {ℓ} {A : Set ℓ} {φ : I} {u : Partial φ A} → A [ φ ↦ u ] → A

They satisfy the following equalities:

.. code-block:: agda

  outS (inS a) = a

  inS {φ = φ} (outS {φ = φ} a) = a

  outS {φ = i1} {u} _ = u 1=1


Note that given ``a : A [ φ ↦ u ]`` and ``α : IsOne φ``, it is not the case
that ``outS a = u α``; however, underneath the pattern binding ``(φ = i1)``,
one has ``outS a = u 1=1``.

With all of this cubical infrastructure we can now describe the
``hcomp`` operations.



Homogeneous composition
=======================

The homogeneous composition operations generalize binary composition
of paths so that we can compose multiple composable cubes.

.. code-block:: agda

  hcomp : ∀ {ℓ} {A : Set ℓ} {φ : I} (u : I → Partial φ A) (u0 : A) → A

When calling ``hcomp {φ = φ} u u0`` Agda makes sure that ``u0`` agrees
with ``u i0`` on ``φ``. The idea is that ``u0`` is the base and ``u``
specifies the sides of an open box. This is hence an open (higher
dimensional) cube where the side opposite of ``u0`` is missing. The
``hcomp`` operation then gives us the missing side opposite of
``u0``. For example binary composition of paths can be written as:

::

  compPath : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  compPath {x = x} p q i = hcomp (λ j → λ { (i = i0) → x
                                          ; (i = i1) → q j })
                                 (p i)

Pictorially we are given ``p : x ≡ y`` and ``q : y ≡ z``, and the
composite of the two paths is obtained by computing the missing lid of
this open square:

.. code-block:: text

          x             z
          ^             ^
          |             |
        x |             | q j
          |             |
          x ----------> y
               p i

In the drawing the direction ``i`` goes left-to-right and ``j`` goes
bottom-to-top. As we are constructing a path from ``x`` to ``z`` along
``i`` we have ``i : I`` in the context already and we put ``p i`` as
bottom. The direction ``j`` that we are doing the composition in is
abstracted in the first argument to ``hcomp``.

Note that the partial element ``u`` does not have to specify
all the sides of the open box, giving more sides simply gives you
more control on the result of ``hcomp``.
For example if we omit the ``(i = i0) → x`` side in the
definition of ``compPath`` we still get a valid term of type
``A``. However, that term would reduce to ``hcomp (\ j → \ { () }) x``
when ``i = i0`` and so that definition would not build
a path that starts from ``x``.

We can also define homogeneous filling of cubes as

::

  hfill : ∀ {ℓ} {A : Set ℓ} {φ : I}
          (u : ∀ i → Partial φ A) (u0 : A [ φ ↦ u i0 ])
          (i : I) → A
  hfill {φ = φ} u u0 i = hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                                        ; (i = i0) → outS u0 })
                               (outS u0)

When ``i`` is ``i0`` this is ``u0`` and when ``i`` is ``i1`` this is
``hcomp u u0``. This can hence be seen as giving us the interior of an
open box. In the special case of the square above ``hfill`` gives us a
direct cubical proof that composing ``p`` with ``refl`` is ``p``.

::

  compPathRefl : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → compPath p refl ≡ p
  compPathRefl {x = x} {y = y} p j i = hfill (λ _ → λ { (i = i0) → x
                                                      ; (i = i1) → y })
                                             (inS (p i))
                                             (~ j)


Glue types
==========

In order to be able to prove the univalence theorem we also have to
add "Glue" types. These lets us turn equivalences between types into
paths between types. An equivalence of types ``A`` and ``B`` is
defined as a map ``f : A → B`` such that its fibers are contractible.

.. code-block:: agda

  fiber : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (y : B) → Set ℓ
  fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

  isContr : ∀ {ℓ} → Set ℓ → Set ℓ
  isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

  record isEquiv {ℓ} {A B : Set ℓ} (f : A → B) : Set ℓ where
    field
      equiv-proof : (y : B) → isContr (fiber f y)

  _≃_ : ∀ {ℓ} (A B : Set ℓ) → Set ℓ
  A ≃ B = Σ[ f ∈ (A → B) ] (isEquiv f)

The simplest example of an equivalence is the identity function.

::

  idfun : ∀ {ℓ} → (A : Set ℓ) → A → A
  idfun _ x = x

  idIsEquiv : ∀ {ℓ} (A : Set ℓ) → isEquiv (idfun A)
  equiv-proof (idIsEquiv A) y =
    ((y , refl) , λ z i → z .snd (~ i) , λ j → z .snd (~ i ∨ j))

  idEquiv : ∀ {ℓ} (A : Set ℓ) → A ≃ A
  idEquiv A = (idfun A , idIsEquiv A)


An important special case of equivalent types are isomorphic types
(i.e. types with maps going back and forth which are mutually
inverse): https://github.com/agda/cubical/blob/master/Cubical/Foundations/Isomorphism.agda.

As everything has to work up to higher dimensions the Glue types take
a partial family of types that are equivalent to the base type ``A``:

::

  Glue : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
       → Partial φ (Σ[ T ∈ Set ℓ' ] T ≃ A) → Set ℓ'

..
  ::

  Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

These come with a constructor and eliminator:

.. code-block:: agda

  glue : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I} {Te : Partial φ (Σ[ T ∈ Set ℓ' ] T ≃ A)}
       → PartialP φ T → A → Glue A Te

  unglue : ∀ {ℓ ℓ'} {A : Set ℓ} (φ : I) {Te : Partial φ (Σ[ T ∈ Set ℓ' ] T ≃ A)}
         → Glue A Te → A


Using Glue types we can turn an equivalence of types into a path as
follows:

::

  ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
  ua {_} {A} {B} e i = Glue B (λ { (i = i0) → (A , e)
                                 ; (i = i1) → (B , idEquiv B) })

The idea is that we glue ``A`` together with ``B`` when ``i = i0``
using ``e`` and ``B`` with itself when ``i = i1`` using the identity
equivalence. This hence gives us the key part of univalence: a
function for turning equivalences into paths. The other part of
univalence is that this map itself is an equivalence which follows
from the computation rule for ``ua``:

::

  uaβ : ∀ {ℓ} {A B : Set ℓ} (e : A ≃ B) (x : A) → transport (ua e) x ≡ e .fst x
  uaβ e x = transportRefl (e .fst x)

Transporting along the path that we get from applying ``ua`` to an
equivalence is hence the same as applying the equivalence. This is
what makes it possible to use the univalence axiom computationally in
Cubical Agda: we can package up our equivalences as paths, do equality
reasoning using these paths, and in the end transport along the paths
in order to compute with the equivalences.

We have the following equalities:

.. code-block:: agda

   Glue A {i1} Te = Te 1=1 .fst

   unglue φ (glue t a) = a

   glue (\ { (φ = i1) -> g}) (unglue φ g) = g

   unglue i1 {Te} g = Te 1=1 .snd .fst g

   glue {φ = i1} t a = t 1=1


For more results about Glue types and univalence see
https://github.com/agda/cubical/blob/master/Cubical/Core/Glue.agda and
https://github.com/agda/cubical/blob/master/Cubical/Foundations/Univalence.agda. For
some examples of what can be done with this for working with binary
and unary numbers see
https://github.com/agda/cubical/blob/master/Cubical/Data/BinNat/BinNat.agda.


Higher inductive types
======================

Cubical Agda also lets us directly define higher inductive types as
datatypes with path constructors. For example the circle and `torus
<https://en.wikipedia.org/wiki/Torus>`_ can be defined as:

::

  data S¹ : Set where
    base : S¹
    loop : base ≡ base

  data Torus : Set where
    point : Torus
    line1 : point ≡ point
    line2 : point ≡ point
    square : PathP (λ i → line1 i ≡ line1 i) line2 line2

Functions out of higher inductive types can then be defined using
pattern-matching:

::

  t2c : Torus → S¹ × S¹
  t2c point        = (base   , base)
  t2c (line1 i)    = (loop i , base)
  t2c (line2 j)    = (base   , loop j)
  t2c (square i j) = (loop i , loop j)

  c2t : S¹ × S¹ → Torus
  c2t (base   , base)   = point
  c2t (loop i , base)   = line1 i
  c2t (base   , loop j) = line2 j
  c2t (loop i , loop j) = square i j

When giving the cases for the path and square constructors we have to
make sure that the function maps the boundary to the right thing. For
instance the following definition does not pass Agda's typechecker as
the boundary of the last case does not match up with the expected
boundary of the square constructor (as the ``line1`` and ``line2``
cases are mixed up).

.. code-block:: agda

  c2t_bad : S¹ × S¹ → Torus
  c2t_bad (base   , base)   = point
  c2t_bad (loop i , base)   = line2 i
  c2t_bad (base   , loop j) = line1 j
  c2t_bad (loop i , loop j) = square i j

Functions defined by pattern-matching on higher inductive types
compute definitionally, for all constructors.

::

  c2t-t2c : ∀ (t : Torus) → c2t (t2c t) ≡ t
  c2t-t2c point        = refl
  c2t-t2c (line1 _)    = refl
  c2t-t2c (line2 _)    = refl
  c2t-t2c (square _ _) = refl

  t2c-c2t : ∀ (p : S¹ × S¹) → t2c (c2t p) ≡ p
  t2c-c2t (base   , base)   = refl
  t2c-c2t (base   , loop _) = refl
  t2c-c2t (loop _ , base)   = refl
  t2c-c2t (loop _ , loop _) = refl

By turning this isomorphism into an equivalence we get a direct proof
that the torus is equal to two circles.

.. code-block:: agda

  Torus≡S¹×S¹ : Torus ≡ S¹ × S¹
  Torus≡S¹×S¹ = isoToPath (iso t2c c2t t2c-c2t c2t-t2c)

Cubical Agda also supports parameterized and recursive higher
inductive types, for example propositional truncation (squash types)
is defined as:

::

  data ∥_∥ {ℓ} (A : Set ℓ) : Set ℓ where
    ∣_∣ : A → ∥ A ∥
    squash : ∀ (x y : ∥ A ∥) → x ≡ y

  isProp : ∀ {ℓ} → Set ℓ → Set ℓ
  isProp A = (x y : A) → x ≡ y

  recPropTrunc : ∀ {ℓ} {A : Set ℓ} {P : Set ℓ} → isProp P → (A → P) → ∥ A ∥ → P
  recPropTrunc Pprop f ∣ x ∣          = f x
  recPropTrunc Pprop f (squash x y i) =
    Pprop (recPropTrunc Pprop f x) (recPropTrunc Pprop f y) i

For many more examples of higher inductive types see:
https://github.com/agda/cubical/tree/master/Cubical/HITs.

.. _indexed-inductive-types:

Indexed inductive types
=======================

Cubical Agda has experimental support for the ``transp`` primitive when
used to substitute the indices of an indexed inductive type. A handful
of definitions (satisfying a technical restriction on their pattern
matching) will compute when applied to a transport along indices. As an
example of what works, let us consider the following running example:

::

  data Eq {a} {A : Set a} (x : A) : A → Set a where
    reflEq : Eq x x

  data Vec {a} (A : Set a) : Nat → Set a where
    []  : Vec A zero
    _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)


Functions which match on ``Eq`` when all of its endpoints are variables,
that is, very generic lemmas like ``symEq`` and ``transpEq`` below, will
compute on all cases: they will compute to the given right-hand-side
definitionally when their argument is ``reflEq``, and will compute to a
transport in the codomain when their argument has been transported in
the second variable.

::

  symEq : ∀ {a} {A : Set a} {x y : A} → Eq x y → Eq y x
  symEq reflEq = reflEq

  transpEq : ∀ {a} {A B : Set a} → Eq A B → A → B
  transpEq reflEq x = x

  pathToEq : ∀ {a} {A : Set a} {x y : A} → x ≡ y → Eq x y
  pathToEq {x = x} p = transp (λ i → Eq x (p i)) i0 reflEq

  module _ {a} {A B : Set a} {x y : A} {f : A ≃ B} where
    _ : symEq (reflEq {x = x}) ≡ reflEq
    _ = refl

    _ : transpEq (pathToEq (ua (idEquiv Bool))) ≡ λ x → x
    _ = refl

Matching on indexed types in situations where types are assumed (so
their transports are also open) often generates many more transports
than the comparable construction with paths would. As an example,
compare the proof of ``uaβEq`` below has four pending transports,
whereas ``uaβ`` only has one!

::

    uaβEq : transpEq (pathToEq (ua f)) ≡ f .fst
    uaβEq = funExt λ z →
      compPath (transportRefl (f .fst _))
        (cong (f .fst) (compPath
          (transportRefl _)
          (compPath
            (transportRefl _)
            (transportRefl _))))

In more concrete situations, such as when the indices are constructors
of some other inductive type, pattern-matching definitions will not
compute when applied to transports. For specific unsupported cases, see
:ref:`cubical-ix-matching`.

If the ``UnsupportedIndexedMatch`` warning is enabled (it is by default),
Agda will print a warning for every definition whose computational
behaviour could not be extended to cover transports. Internally,
transports are represented by an additional constructor, and
pattern-matching definitions must be extended to cover these
constructors. To do this, the results of pattern-matching unification
must be translated into an embedding (in the HoTT sense).
**This is work-in-progress.**

For the day-to-day use of Cubical Agda, it is advisable to disable the
``UnsupportedIndexedMatch`` warnings. You can do this using the
``-WnoUnsupportedIndexedMatch`` option in an ``OPTIONS`` pragma or in your
``agda-lib`` file.

.. _cubical-ix-matching:

What works, and what doesn't
----------------------------

This section lists some of the common cases where pattern-matching
unification produces something that can not be extended to cover
transports, and the cases in which it can.

The following pair of definitions relies on injectivity for data
constructors (specifically of the constructor ``suc``), and so will not
compute on transported values.

::


  sucInjEq : ∀ {n k} → Eq (suc n) (suc k) → Eq n k
  sucInjEq reflEq = reflEq

  head : ∀ {n} {a} {A : Set a} → Vec A (suc n) → A
  head (x ∷ _) = x

To demonstrate the failure of computation, we can set up the following
artificial example using ``head``. By passing the vector ``true ∷ []``
through two transports, even if they would cancel out, ``head``'s
computation gets stuck.

::

  module _ (n : Nat) (p : n ≡ 1) where private
    vec : Vec Bool n
    vec = transport (λ i → Vec Bool (p (~ i))) (true ∷ [])

    hd : Bool
    hd = head (transport (λ i → Vec Bool (p i)) vec)

  -- Does not type-check:
  -- _ : hd ≡ true
  -- _ = refl
  -- Instead, hd is some big expression involving head applied to a
  -- transport

If a definition is stuck on a transport, often the best workaround is to
avoid treating it like the reducible expression it should be, and
managing the transports yourself. For example, using the proof that
``transport (sym p) (transport p x) ≡ x``, we can compute with ``hd`` up
to a path, even if it's definitionally stuck.

::

  -- Continuing from above..

    _ : hd ≡ true
    _ = cong head (transport⁻Transport (λ i → Vec Bool (p (~ i))) (true ∷ []))


In other cases, it may be possible to rephrase the proof in ways that
avoid unsupported cases in pattern matching, and so, compute. For
example, returning to ``sucInj``, we can define it in terms of ``apEq``
(which always computes), and the fact that ``suc`` has a
partially-defined inverse:

::

  apEq : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y : A}
       → Eq x y → Eq (f x) (f y)
  apEq f reflEq = reflEq

  sucInjEq′ : ∀ {n k} → Eq (suc n) (suc k) → Eq n k
  sucInjEq′ = apEq λ { (suc n) → n ; zero → zero }

Definitions which rely on principles incompatible with Cubical Agda (K,
injectivity of type constructors) will never compute on transports. Note
that enabling both Cubical and K is not compatible with :option:`--safe`.

Absurd clauses do not need any special handling (since the transport of
an absurdity is still absurd), so definitions which rely on Agda's
ability to automatically separate constructors of inductive types will
not generate a ``UnsupportedIndexedMatch`` warning.

::

  zeroNotSucEq : ∀ {n} {a} {A : Set a} → Eq zero (suc n) → A
  zeroNotSucEq ()

Definitions whose elaboration involves using an equality derived from
pattern-matching in a type in ``Setω`` can not be extended yet. The
following example is very artificial because it minimises
`an example from the Cubical library <https://github.com/agda/cubical/blob/2131b6c08e32fdcf5b9292e5c6d6f23e4bf80fcd/Cubical/Structures/Macro.agda>`_.
The point is that to extend ``test`` to cover transports, we would need
to, given ``p : ℓ′ ≡ ℓ``, produce a ``PathP (λ i → Argh ℓ (p i)) _ _``,
but ``Setω`` is not considered fibrant yet.

::

  data Argh (ℓ : Level) : Level → Setω where
    argh : ∀ {ℓ′} → Argh ℓ ℓ′ → Argh ℓ ℓ′

  test : ∀ {ℓ ℓ′} → Argh ℓ ℓ′ → Bool
  test {ℓ} (argh _) = true


Modalities & indexed matching
-----------------------------

When using indexed matching in Cubical Agda, clauses' arguments (and
their right-hand-sides) need to be transported to account for indexing,
meaning that the *types* of those arguments must be well-formed *terms*.

For example, the following code is forbidden in Cubical Agda, and when
``--without-K`` is enabled:

.. code-block:: agda

  subst : (@0 P : A → Set p) → x ≡ y → P x → P y
  subst _ refl p = p

This is because the predicate ``P`` is erased, but internally, we have
to transport along the argument ``p`` along a path involving ``P``, in a
relevant position.

Any argument which is used in the result type, or appears after a forced
(dot) pattern, must have a modality-correct type.

Cubical identity types and computational HoTT/UF
================================================

As mentioned above the computation rule for ``J`` does not hold
definitionally for path types. Cubical Agda solves this by introducing
a cubical identity type. The
https://github.com/agda/cubical/blob/master/Cubical/Core/Id.agda file
exports all of the primitives for this type, including the notation
``_≡_`` and a ``J`` eliminator that computes definitionally on
``refl``.

The cubical identity types and path types are equivalent, so all of
the results for one can be transported to the other one (using
univalence). Using this we have implemented an `interface to HoTT/UF <https://github.com/agda/cubical/blob/5de11df25b79ee49d5c084fbbe6dfc66e4147a2e/Cubical/Experiments/HoTT-UF.agda>`_
which provides the user with the key primitives of Homotopy Type
Theory and Univalent Foundations implemented using cubical primitives
under the hood. This hence gives an axiom free version of HoTT/UF
which computes properly.

.. code-block:: agda

  module Cubical.Core.HoTT-UF where

  open import Cubical.Core.Id public
     using ( _≡_            -- The identity type.
           ; refl           -- Its constructor.
           ; J              -- Its eliminator (can be defined by pattern matching)

           ; transport      -- As in the HoTT Book.
           ; ap
           ; _∙_
           ; _⁻¹

           ; _≡⟨_⟩_         -- Standard equational reasoning.
           ; _∎

           ; funExt         -- Function extensionality
                            -- (can also be derived from univalence).

           ; Σ              -- Sum type. Needed to define contractible types, equivalences
           ; _,_            -- and univalence.
           ; pr₁            -- The eta rule is available.
           ; pr₂

           ; isProp         -- The usual notions of proposition, contractible type, set.
           ; isContr
           ; isSet

           ; isEquiv        -- A map with contractible fibers
                            -- (Voevodsky's version of the notion).
           ; _≃_            -- The type of equivalences between two given types.
           ; EquivContr     -- A formulation of univalence.

           ; ∥_∥             -- Propositional truncation.
           ; ∣_∣             -- Map into the propositional truncation.
           ; ∥∥-isProp       -- A truncated type is a proposition.
           ; ∥∥-recursion    -- Non-dependent elimination.
           ; ∥∥-induction    -- Dependent elimination.
           )

In order to get access to only the HoTT/UF primitives start a file as
follows:

.. code-block:: agda

  {-# OPTIONS --cubical #-}

  open import Cubical.Core.HoTT-UF

However, even though this interface exists, we recommend that users of
cubical mode use the path types rather than the cubical identity types.
Primarily, this is because many operations for path types are
implemented directly, rather than by induction (e.g. ``ap``, ``funExt``,
``happly``, ``sym``, etc), and thus enjoy better computational
behaviour. In addition to using ``J`` directly, it is possible to match
on the reflexivity constructor, as if ``Id`` were an inductive type:

::

  symId : ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → Id y x
  symId reflId = reflId

Cubical identity types are *not* inductively defined, and we may observe
this using the primitives ``conid`` and ``primIdElim``. These primitives
expose underlying representation: terms of the cubical identity type can
be thought of pairs consisting of a path `p` and a cofibration `φ`, such
that, under the cofibration `φ`, the path `p` is the reflexivty path.
These primitives are very low-level, and their use is not recommended.

::

  apId : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} (f : A → B)
       → {x y : A} → Id x y → Id (f x) (f y)
  apId f {x = x} = primIdElim (λ y _ → Id (f x) (f y))
    λ φ y w → conid φ λ i → f (outS w i)

Even though it is possible to define the reflexivity path using
``conid``, the name ``reflId`` is special, in that it is treated as a
"matchable" constructor, whereas ``conid`` is not. Depending on your
syntax highlighting scheme, this can be observed using agda-mode: they
are different colours. However, for computation, they are treated as the
same:

::

  _ : ∀ {ℓ} {A : Set ℓ} {x : A} → reflId ≡ conid i1 (λ _ → x)
  _ = refl

.. _erased-cubical:

Cubical Agda with erased Glue
=============================

The option :option:`--erased-cubical` enables a variant of Cubical
Agda in which Glue (and the other builtins defined in
``Agda.Builtin.Cubical.Glue``) must only be used in
:ref:`erased<runtime-irrelevance>` settings.

Regular Cubical Agda code can import code that uses
:option:`--erased-cubical`. Regular Cubical Agda code can also be
imported from code that uses :option:`--erased-cubical`, but names
defined using Cubical Agda are treated as if they had been marked as
erased, with an exception related to pattern matching:

- Matching on a non-erased imported constructor does not, on its own,
  make Agda treat the right-hand side as erased.

The reason for this exception is that it should be possible to import
the code from modules that use :option:`--cubical`, in which the
non-erased constructors are not treated as erased.

Note that names that are re-exported from a Cubical Agda module using
``open import M args public`` are seen as defined using Cubical Agda.

References
==========

.. _`CCHM`:

  Cyril Cohen, Thierry Coquand, Simon Huber and Anders Mörtberg;
  `“Cubical Type Theory: a constructive interpretation of the
  univalence axiom” <https://arxiv.org/abs/1611.02108>`_.

.. _`CHM`:

  Thierry Coquand, Simon Huber, Anders Mörtberg; `"On Higher Inductive
  Types in Cubical Type Theory" <https://arxiv.org/abs/1802.01170>`_.


.. _primitives-ref:

Appendix: Cubical Agda primitives
=================================

The Cubical Agda primitives and internals are exported by a series of
files found in the ``lib/prim/Agda/Builtin/Cubical`` directory of
Agda. The ``agda/cubical`` library exports all of these primitives
with the names used throughout this document. Experts might find it
useful to know what is actually exported as there are quite a few
primitives available that are not really exported by ``agda/cubical``,
so the goal of this section is to list the contents of these
files. However, for regular users and beginners the ``agda/cubical``
library should be sufficient and this section can safely be ignored.

**Warning**: Many of the built-ins whose definitions can be written in
Agda are nonetheless used internally in the implementation of cubical Agda,
and using different implementations can easily lead to unsoundness. Even
though they are definable in user code, this is not a supported
use-case.

The key file with primitives is ``Agda.Primitive.Cubical``. It exports
the following ``BUILTIN``, primitives and postulates:

.. code-block:: agda

  {-# BUILTIN CUBEINTERVALUNIV IUniv #-}  -- IUniv : SSet₁
  {-# BUILTIN INTERVAL I  #-}  -- I : IUniv
  {-# BUILTIN IZERO    i0   #-}
  {-# BUILTIN IONE     i1   #-}

  infix 30 primINeg
  infixr 20 primIMin primIMax

  primitive
    primIMin : I → I → I   -- _∧_
    primIMax : I → I → I   -- _∨_
    primINeg : I → I       -- ~_

  {-# BUILTIN ISONE IsOne #-} -- IsOne : I → SSet

  postulate
    itIsOne : IsOne i1     -- 1=1
    IsOne1  : ∀ i j → IsOne i → IsOne (primIMax i j)
    IsOne2  : ∀ i j → IsOne j → IsOne (primIMax i j)

  {-# BUILTIN ITISONE      itIsOne  #-}
  {-# BUILTIN ISONE1       IsOne1   #-}
  {-# BUILTIN ISONE2       IsOne2   #-}
  {-# BUILTIN PARTIAL      Partial  #-}
  {-# BUILTIN PARTIALP     PartialP #-}

  postulate
    isOneEmpty : ∀ {a} {A : Partial i0 (Set a)} → PartialP i0 A
  {-# BUILTIN ISONEEMPTY isOneEmpty #-}

  primitive
    primPOr : ∀ {a} (i j : I) {A : Partial (primIMax i j) (Set a)}
            → PartialP i (λ z → A (IsOne1 i j z)) → PartialP j (λ z → A (IsOne2 i j z))
            → PartialP (primIMax i j) A

    -- Computes in terms of primHComp and primTransp
    primComp : ∀ {a} (A : (i : I) → Set (a i)) {φ : I} → (∀ i → Partial φ (A i)) → (a : A i0) → A i1

  syntax primPOr p q u t = [ p ↦ u , q ↦ t ]

  primitive
    primTransp : ∀ {a} (A : (i : I) → Set (a i)) (φ : I) → (a : A i0) → A i1
    primHComp : ∀ {a} {A : Set a} {φ : I} → (∀ i → Partial φ A) → A → A

The interval ``I`` belongs to its own sort, ``IUniv``. Types in this sort
do not support composition and transport (unlike ``Set``), but function
types from types in this sort to types in ``Set`` do (unlike `SSet`).

The Path types are exported by ``Agda.Builtin.Cubical.Path``:

.. code-block:: agda

  postulate
    PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

  {-# BUILTIN PATHP        PathP     #-}

  infix 4 _≡_
  _≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
  _≡_ {A = A} = PathP (λ _ → A)

  {-# BUILTIN PATH         _≡_     #-}

The Cubical subtypes are exported by ``Agda.Builtin.Cubical.Sub``:

.. code-block:: agda

  {-# BUILTIN SUB Sub #-}

  postulate
    inc : ∀ {ℓ} {A : Set ℓ} {φ} (x : A) → Sub A φ (λ _ → x)

  {-# BUILTIN SUBIN inS #-}

  primitive
    primSubOut : ∀ {ℓ} {A : Set ℓ} {φ : I} {u : Partial φ A} → Sub _ φ u → A

The Glue types are exported by ``Agda.Builtin.Cubical.Glue``:

.. code-block:: agda

  record isEquiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ ⊔ ℓ') where
    field
      equiv-proof : (y : B) → isContr (fiber f y)
  infix 4 _≃_

  _≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
  A ≃ B = Σ (A → B) \ f → (isEquiv f)

  equivFun : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → A → B
  equivFun e = fst e

  equivProof : ∀ {la lt} (T : Set la) (A : Set lt) → (w : T ≃ A) → (a : A)
             → ∀ ψ (f : Partial ψ (fiber (w .fst) a)) → fiber (w .fst) a [ ψ ↦ f ]
  equivProof A B w a ψ fb = contr' {A = fiber (w .fst) a} (w .snd .equiv-proof a) ψ fb
    where
      contr' : ∀ {ℓ} {A : Set ℓ} → isContr A → (φ : I) → (u : Partial φ A) → A
      contr' {A = A} (c , p) φ u = hcomp (λ i → λ { (φ = i1) → p (u 1=1) i
                                                  ; (φ = i0) → c }) c

  {-# BUILTIN EQUIV      _≃_        #-}
  {-# BUILTIN EQUIVFUN   equivFun   #-}
  {-# BUILTIN EQUIVPROOF equivProof #-}

  primitive
    primGlue    : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
      → (T : Partial φ (Set ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
      → Set ℓ'
    prim^glue   : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
      → PartialP φ T → A → primGlue A T e
    prim^unglue : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
      → primGlue A T e → A
    primFaceForall : (I → I) → I

  -- pathToEquiv proves that transport is an equivalence (for details
  -- see Agda.Builtin.Cubical.Glue). This is needed internally.
  {-# BUILTIN PATHTOEQUIV pathToEquiv #-}

Note that the Glue types are uncurried in ``agda/cubical`` to make
them more pleasant to use:

.. code-block:: agda

  Glue : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
       → (Te : Partial φ (Σ[ T ∈ Set ℓ' ] T ≃ A))
       → Set ℓ'
  Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

The ``Agda.Builtin.Cubical.Id`` exports the cubical identity types:

.. code-block:: agda

  postulate
    Id : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ

  {-# BUILTIN ID           Id       #-}
  {-# BUILTIN CONID        conid    #-}
  {-# BUILTIN REFLID       reflId   #-}

  primitive
    primDepIMin : _
    primIdFace : ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → I
    primIdPath : ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → x ≡ y

  primitive
    primIdElim : ∀ {a c} {A : Set a} {x : A}
                   (C : (y : A) → Id x y → Set c) →
                   ((φ : I) (y : A [ φ ↦ (λ _ → x) ])
                    (w : (x ≡ outS y) [ φ ↦ (λ { (φ = i1) → \ _ → x}) ]) →
                    C (outS y) (conid φ (outS w))) →
                   {y : A} (p : Id x y) → C y p
