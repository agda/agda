..
  ::

  {-# OPTIONS --cubical #-}
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
    renaming ( primSubOut to outS
             ; inc        to inS
             )
  open import Agda.Builtin.Cubical.Glue public
    using ( isEquiv
          ; equiv-proof
          ; _≃_
          ; primGlue )

  open import Agda.Builtin.Sigma public
  open import Agda.Builtin.Bool public

  infix 2 Σ-syntax

  Σ-syntax : ∀ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') → Set (ℓ ⊔ ℓ')
  Σ-syntax = Σ

  syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

  _×_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
  A × B = Σ A (λ _ → B)

  infixr 5 _×_

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
OPTIONS --cubical #-}`` at the top of the file.

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
https://homotopytypetheory.org/2018/12/06/cubical-agda/ (lagda rendered
version: https://ice1000.org/lagda/CubicalAgdaLiterate.html).

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
---------------------------

The key idea of Cubical Type Theory is to add an interval type ``I :
Setω`` (the reason this is in ``Setω`` is because it doesn't support
the ``transp`` and ``hcomp`` operations). A variable ``i : I``
intuitively corresponds to a point the `real unit interval
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
---------

While path types are great for reasoning about equality they don't let
us transport along paths between types or even compose paths, which in
particular means that we cannot yet prove the induction principle for
paths. In order to remedy this we also have a built-in (generalized)
transport operation and homogeneous composition operations. The
transport operation is generalized in the sense that it lets us
specify where it is the identity function.

.. code-block:: agda

  transp : ∀ {ℓ} (A : I → Set ℓ) (r : I) (a : A i0) → A i1

There is an additional side condition to be satisfied for ``transp A r
a`` to type-check, which is that ``A`` has to be *constant* on
``r``. This means that ``A`` should be a constant function whenever
the constraint ``r = i1`` is satisfied.  This side condition is
vacuously true when ``r`` is ``i0``, so there is nothing to check when
writing ``transp A i0 a``. However when ``r`` is equal to ``i1`` the
``transp`` function will compute as the identity function.

.. code-block:: agda

   transp A i1 a = a

This requires ``A`` to be constant for it to be well-typed.

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
----------------

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

  Partial : ∀ {ℓ} → I → Set ℓ → Setω

  PartialP : ∀ {ℓ} → (φ : I) → Partial φ (Set ℓ) → Setω

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

  _[_↦_] : ∀ {ℓ} (A : Set ℓ) (φ : I) (u : Partial φ A) → Setω
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

  inS {u = u} (outS {u = u} a) = a

  outS {φ = i1} {u} _ = u 1=1


With all of this cubical infrastructure we can now describe the
``hcomp`` operations.



Homogeneous composition
-----------------------

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

Note that the partial element ```u``` does not have to specify
all the sides of the open box, giving more sides simply gives you
more control on the result of ```hcomp```.
For example if we omit the ```(i = i0) → x``` side in the
definition of ```compPath``` we still get a valid term of type
```A```. However, that term would reduce to ```hcomp (\ j → \ { () }) x```
when ```i = i0``` and so that definition would not build
a path that starts from ```x```.

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
----------

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
----------------------

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

Cubical identity types and computational HoTT/UF
------------------------------------------------

As mentioned above the computation rule for ``J`` does not hold
definitionally for path types. Cubical Agda solves this by introducing
a cubical identity type. The
https://github.com/agda/cubical/blob/master/Cubical/Core/Id.agda file
exports all of the primitives for this type, including the notation
``_≡_`` and a ``J`` eliminator that computes definitionally on
``refl``.

The cubical identity type and the path type are equivalent, so all of
the results for one can be transported to the other one (using
univalence). Using this we have implemented an interface to HoTT/UF in
https://github.com/agda/cubical/blob/master/Cubical/Core/HoTT-UF.agda
which provides the user with the key primitives of Homotopy Type
Theory and Univalent Foundations implemented using cubical primitives
under the hood. This hence gives an axiom free version of HoTT/UF
which computes properly.

.. code-block:: agda

  module Cubical.Core.HoTT-UF where

  open import Cubical.Core.Id public
     using ( _≡_            -- The identity type.
           ; refl            -- Unfortunately, pattern matching on refl is not available.
           ; J              -- Until it is, you have to use the induction principle J.

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

However, even though this interface exists it is still recommended
that one uses the cubical identity types unless one really need ``J``
to compute on ``refl``. The reason for this is that the syntax for
path types does not work for the identity types, making many proofs
more involved as the only way to reason about them is using ``J``.
Furthermore, the path types satisfy many useful definitional
equalities that the identity types don't.

References
----------

.. _`CCHM`:

  Cyril Cohen, Thierry Coquand, Simon Huber and Anders Mörtberg;
  `“Cubical Type Theory: a constructive interpretation of the
  univalence axiom” <https://arxiv.org/abs/1611.02108>`_.

.. _`CHM`:

  Thierry Coquand, Simon Huber, Anders Mörtberg; `"On Higher Inductive
  Types in Cubical Type Theory" <https://arxiv.org/abs/1802.01170>`_.


.. _primitives-ref:

Appendix: Cubical Agda primitives
---------------------------------

The Cubical Agda primitives and internals are exported by a series of
files found in the ``lib/prim/Agda/Builtin/Cubical`` directory of
Agda. The ``agda/cubical`` library exports all of these primitives
with the names used throughout this document. Experts might find it
useful to know what is actually exported as there are quite a few
primitives available that are not really exported by ``agda/cubical``,
so the goal of this section is to list the contents of these
files. However, for regular users and beginners the ``agda/cubical``
library should be sufficient and this section can safely be ignored.

The key file with primitives is ``Agda.Primitive.Cubical``. It exports
the following ``BUILTIN``, primitives and postulates:

.. code-block:: agda

  {-# BUILTIN INTERVAL I    #-} -- I : Setω
  {-# BUILTIN IZERO    i0   #-}
  {-# BUILTIN IONE     i1   #-}

  infix 30 primINeg
  infixr 20 primIMin primIMax

  primitive
    primIMin : I → I → I   -- _∧_
    primIMax : I → I → I   -- _∨_
    primINeg : I → I       -- ~_

  {-# BUILTIN ISONE IsOne #-} -- IsOne : I → Setω

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
    primComp : ∀ {a} (A : (i : I) → Set (a i)) (φ : I) → (∀ i → Partial φ (A i)) → (a : A i0) → A i1

  syntax primPOr p q u t = [ p ↦ u , q ↦ t ]

  primitive
    primTransp : ∀ {a} (A : (i : I) → Set (a i)) (φ : I) → (a : A i0) → A i1
    primHComp : ∀ {a} {A : Set a} {φ : I} → (∀ i → Partial φ A) → A → A

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
             → ∀ ψ → (Partial ψ (fiber (w .fst) a)) → fiber (w .fst) a
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

  primitive
    primDepIMin : _
    primIdFace : ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → I
    primIdPath : ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → x ≡ y

  primitive
    primIdJ : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : ∀ y → Id x y → Set ℓ') →
                P x (conid i1 (λ i → x)) → ∀ {y} (p : Id x y) → P y p


  primitive
    primIdElim : ∀ {a c} {A : Set a} {x : A}
                   (C : (y : A) → Id x y → Set c) →
                   ((φ : I) (y : A [ φ ↦ (λ _ → x) ])
                    (w : (x ≡ outS y) [ φ ↦ (λ { (φ = i1) → \ _ → x}) ]) →
                    C (outS y) (conid φ (outS w))) →
                   {y : A} (p : Id x y) → C y p

