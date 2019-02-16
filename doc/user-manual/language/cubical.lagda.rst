..
  ::
  {-# OPTIONS --cubical #-}
  module language.cubical where

  open import Agda.Primitive.Cubical
                         renaming ( primIMin to _∧_
                                  ; primIMax to _∨_
                                  ; primINeg to ~_
                                  ; isOneEmpty to empty
                                  ; primHComp to hcomp
                                  ; primTransp to transp
                                  ; itIsOne to 1=1 )
  open import Agda.Builtin.Cubical.Path renaming (_≡_ to Path)

.. _cubical:

***************************
Cubical Type Theory in Agda
***************************

As of 2.6.0 Agda has a cubical mode which extends Agda with a variety
of features from Cubical Type Theory. In particular, computational
univalence and higher inductive types.

The version of Cubical Type Theory that Agda implements is a variation
of `CCHM`_ where the Kan composition operations are decomposed into
homogeneous composition and generalized transport. This is what makes
the general schema for higher inductive types work, following `CHM`_.

To use cubical type theory, you need to run Agda with the
``--cubical`` command-line-option or put ``{-# OPTIONS --cubical #-}``
at the top of the file.

The cubical mode adds the following features to Agda:

1. An interval ``I`` type and path types
2. Partial elements and systems
3. Kan operations (``transp`` and ``hcomp``)
4. ``Glue`` types
5. Higher inductive types
6. Cubical identity types

There is a standard library for Cubical Agda available at
https://github.com/agda/cubical.

The main design choices of the core part of the library are explained
in https://homotopytypetheory.org/2018/12/06/cubical-agda/.

In order to get access to the Cubical Agda primitives one should
either import
https://github.com/agda/cubical/blob/master/Cubical/Core/Primitives.agda
or add the relevant import statements from the top of that file.

There is also an older version of the library available at
https://github.com/Saizan/cubical-demo/.

The interval and path types
---------------------------

The key idea of cubical type theory is to add an interval type ``I :
Setω`` (the reason this is in ``Setω`` is because it doesn't support
the Kan operations).

A variable ``i : I`` intuitively corresponds to a point the `real unit
interval <https://en.wikipedia.org/wiki/Unit_interval>`_. In a closed
context, there are only two values of type ``I``: the two endpoints of
the interval, ``i0`` and ``i1``::

  a b : I
  a = i0
  b = i1

Elements of the interval form a `De Morgan algebra
<https://en.wikipedia.org/wiki/De_Morgan_algebra>`_, with minimum
(``∧``), maximum (``∨``) and negation (``~``).

.. code-block:: agda

  module interval-example₁ (i j : I) where
    data _≡_ (i : I) : I → Set where
      reflI : i ≡ i

    infix 10 _≡_

    max min neg : I

.. code-block:: agda

    max = i ∨ j
    min = i ∧ j
    neg = ~ i

All the properties of de Morgan algebras hold definitionally. The
endpoints of the interval ``i0`` and ``i1`` are the bottom and top
elements, respectively

.. code-block:: agda

    p₁ : i0 ∨ i    ≡ i
    p₂ : i  ∨ i1   ≡ i1
    p₃ : i  ∨ j    ≡ j ∨ i
    p₄ : i  ∧ j    ≡ j ∧ i
    p₅ : ~ (~ i)   ≡ i
    p₆ : i0        ≡ ~ i1
    p₇ : ~ (i ∨ j) ≡ ~ i ∧ ~ j
    p₈ : ~ (i ∧ j) ≡ ~ i ∨ ~ j

.. code-block:: agda

    p₁ = reflI
    p₂ = reflI
    p₃ = reflI
    p₄ = reflI
    p₅ = reflI
    p₆ = reflI
    p₇ = reflI
    p₈ = reflI



The core idea of homotopy type theory is a correspondence between
paths and (proof-relevant) equality. This is taken very literally in
Cubical Type Theory where a path in a type ``A`` is defined as a
function out of the interval, ``I → A``. To define paths we hence use
λ-abstractions. For example, this is the definition of the constant
path:

..
  ::
  module refl-example where

::

    refl : ∀ {a} {A : Set a} {x : A} → Path x x
    refl {x = x} = λ i → x

Although they use the same syntax, a path is not a function. For
example, the following is not valid:

.. code-block:: agda

  refl : ∀ {a} {A : Set a} {x : A} → Path x x
  refl {x = x} = λ (i : I) → x

A ``Path`` is in fact a special case of the more general built-in
heterogeneous path type:

.. code-block:: agda

   PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

   -- Non dependent path types
   Path : ∀ {ℓ} (A : Set ℓ) → A → A → Set ℓ
   Path A a b = PathP (λ _ → A) a b


Because of the intuitions that paths correspond to equality ``PathP (λ
i → A) x y`` gets printed as ``x ≡ y`` when ``A`` does not mention
``i``.

By mapping out of more elements of the interval we can define squares,
cubes, and higher cubes in Agda, making the type theory "cubical".

For example a square in ``A`` is built out of 4 points and 4 lines:

.. code-block:: agda

  Square : ∀ {ℓ} {A : Set ℓ} {a0 a1 b0 b1 : A} →
             a0 ≡ a1 → b0 ≡ b1 → a0 ≡ b0 → a1 ≡ b1 → Set ℓ
  Square p q r s = PathP (λ i → p i ≡ q i) r s

Viewing equalities as functions out of the interval makes it possible
to do a lot of equality reasoning in a very direct way:

.. code-block:: agda

  sym : ∀ {ℓ} {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym p = λ i → p (~ i)

  cong : ∀ {ℓ} {A : Set} {x y : A} {B : A → Set ℓ'}
           (f : (a : A) → B a) (p : x ≡ y)
         → PathP (λ i → B (p i)) (f x) (f y)
  cong f p = λ i → f (p i)

Because of the way functions compute these satisfy some new
definitional equalities:

.. code-block:: agda

  sym sym = id
  cong refl = refl
  cong (f o g) = cong f o cong g

that are not available in standard Agda. Furthermore, path types lets
us prove new things are not true provable in standard Agda, for
example function extensionality (pointwise equal functions are equal):

.. code-block:: agda

  funExt : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x} →
             ((x : A) → f x ≡ g x) → f ≡ g
  funExt p i x = p x i


Partial elements and systems
----------------------------

Path types lets us specify n-dimensional cubes, it is also useful to
be able to specify subcubes. Given an element of the interval ``r :
I`` there is a predicate ``IsOne`` which represents the constraint ``r
= i1``. This comes with a proof that ``ì1`` is actually ``i1`` called
``1=1 : IsOne i1``.

Using this we introduce a type of partial elements called ``Partial r
a``, this is a special version of ``IsOne r → A`` with a more
extensional judgmental equality. There is also a dependent version
version called ``PartialP r A`` which allows ``A`` to be defined only
when ``IsOne r``. The types of these are:

.. code-block:: agda

  Partial : ∀ {ℓ} → I → Set ℓ → Setω

  PartialP : ∀ {ℓ} → (φ : I) → Partial φ (Set ℓ) → Setω

Partial elements are introduced by pattern matching:

.. code-block:: agda

  sys : ∀ i → Partial (i ∨ ~ i) Set₁
  sys i (i = i0) = Set
  sys i (i = i1) = Set → Set

It also works with pattern matching lambdas:
http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.PatternMatchingLambdas

.. code-block:: agda

  sys' : ∀ i → Partial (i ∨ ~ i) Set₁
  sys' i = λ { (i = i0) → Set
             ; (i = i1) → Set → Set }

When the cases overlap they must agree:

.. code-block:: agda

  sys2 : ∀ i j → Partial (i ∨ (i ∧ j)) Set₁
  sys2 i j = λ { (i = i1)          → Set
               ; (i = i1) (j = i1) → Set }

Furthermore ``IsOne i0`` is actually absurd

.. code-block:: agda

  sys3 : Partial i0 Set₁
  sys3 = λ { () }

There are cubical subtypes as in CCHM:

.. code-block:: agda

  _[_↦_] : ∀ {ℓ} (A : Set ℓ) (r : I) (u : Partial r A) → Setω
  A [ r ↦ u ] = Sub A r u

Any element ``u : A`` can be seen as an element of ``A [ r ↦ u ]``
which agrees with ``u`` on ``r``:

.. code-block:: agda

  inc : ∀ {ℓ} {A : Set ℓ} {r : I} (u : A) → A [ r ↦ (λ _ → u) ]

One can also forget that an element agrees with ``u`` on ``r``:

.. code-block:: agda

  ouc : ∀ {ℓ} {A : Set ℓ} {r : I} {u : Partial r A} → A [ r ↦ u ] → A


Kan operations (``transp`` and ``hcomp``)
-----------------------------------------

While path types are great for reasoning about equality they don't
natively let us transport or compose, which in particular means that
we cannot prove the induction principle for paths. In order to remedy
this we also have a builtin (generalized) transport operation and
homogeneous composition. The transport operation is generalized in the
sense that it lets us specify where the operation is the identity
function

.. code-block:: agda

  transp : ∀ {ℓ} (A : I → Set ℓ) (φ : I) (a : A i0) → A i1

When calling ``transp A φ a`` Agda makes sure that ``A`` is constant
on ``φ``. This lets us define regular transport as

.. code-block:: agda

  transport : {A B : Set ℓ} → A ≡ B → A → B
  transport p a = transp (λ i → p i) i0 a

Combining the transport operation with the min operation lets us
define path induction:

.. code-block:: agda

  module _ (P : ∀ y → x ≡ y → Set ℓ') (d : P x refl) where
    J : (p : x ≡ y) → P y p
    J p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

One subtle difference between this and the propositional equality type
of Agda is that the computation rule does not hold definitionally. If
the eliminator is defined using pattern-matching as in the standard
library this holds, however as transport in a constant family is only
the identity function up to a path we have to prove:

.. code-block:: agda

  transportRefl : (x : A) → transport refl x ≡ x
  transportRefl {A = A} x i = transp (λ _ → A) i x

  JRefl : J refl ≡ d
  JRefl = transportRefl d

The homogeneous composition operations generalizes binary composition
of paths so that we can compose multiple composable cubes.

.. code-block:: agda

  hcomp : ∀ {ℓ} {A : Set ℓ} {φ : I} (u : I → Partial φ A) (a : A) → A

When calling ``hcomp {φ = φ} u a`` Agda makes sure that ``a`` agrees
with ``u i0`` on ``φ``. The idea is that ``a`` is the base of the
composition problem and ``u`` specify the sides of the problem so that
we get an open higher dimensional cube (maybe with some sides missing)
where the side opposite of ``a`` is missing. The ``hcomp`` operation
then gives us the missing side of the cube. For example binary
composition of paths can be written as

.. code-block:: agda

  compPath : x ≡ y → y ≡ z → x ≡ z
  compPath p q i =
    hcomp (λ j → \ { (i = i0) → p i0
                   ; (i = i1) → q j }) (p i)

Given ``p : x ≡ y`` and ``q : y ≡ z`` the composite of the two paths
is obtained from a composition of this open square:

.. code-block::

          x   -   -   -   - > z
          ^                   ^
          |                   |
          |                   |
        x |                   | q j
          |                   |
          |                   |
          |                   |
          x ----------------> y
                   p i

The composition is the dashed line at the top of the square. The
direction ``i`` goes left-to-right and ``j`` goes down-to-up. As we
are constructing a path from ``x`` to ``z`` we have ``i : I`` in the
context already which is why we have to put ``p i`` as bottom. The
direction ``j`` that we are doing the composition in is abstracted in
the first argument to ``hcomp``.

We can also define homogeneous filling of cubes as

.. code-block:: agda

  hfill : {A : Set ℓ}
          {φ : I}
          (u : ∀ i → Partial φ A)
          (u0 : A [ φ ↦ u i0 ])
          -----------------------
          (i : I) → A
  hfill {φ = φ} u u0 i =
    hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                   ; (i = i0) → ouc u0 })
          (ouc u0)

When ``i`` is ``i0`` this is ``u0`` and when ``i`` is ``i1`` this is
``hcomp``.


Glue types
----------

In order to be able to prove the univalence axiom we also have Glue
types. These lets us turn equivalences between types into paths. An
equivalence of types ``A`` and ``B`` is defined as a map ``f : A → B``
such that its fibers are contractible.

.. code-block:: agda

  fiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ-max ℓ ℓ')
  fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

  isContr : ∀ {ℓ} → Set ℓ → Set ℓ
  isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

  record isEquiv {ℓ} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ-max ℓ ℓ') where
    field
      equiv-proof : (y : B) → isContr (fiber f y)

  _≃_ : ∀ {ℓ} (A : Set ℓ) (B : Set ℓ') → Set (ℓ-max ℓ ℓ')
  A ≃ B = Σ[ f ∈ (A → B) ] (isEquiv f)

As everything has to work up to higher dimensions the Glue types take
a partial family of types that are equivalent to the base type:

.. code-block:: agda

  Glue : ∀ (A : Set ℓ) {φ : I}
         → (Te : Partial φ (Σ[ T ∈ Set ℓ' ] T ≃ A))
         → Set ℓ'

These come with a constructor and eliminator:

.. code-block:: agda

         glue         -- ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I} {T : Partial φ (Set ℓ')}
                                         -- → {e : PartialP φ (λ o → T o ≃ A)}
                                         -- → PartialP φ T → A → primGlue A T e

         unglue : ∀ {A : Set ℓ} (φ : I) {T : Partial φ (Set ℓ')}
           {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A

Using Glue types we can turn an equivalence of types into a path as follows:

.. code-block:: agda

  ua : ∀ {A B : Set ℓ} → A ≃ B → A ≡ B
  ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                     ; (i = i1) → (B , idEquiv B) })

The idea is that we glue on ``A`` to ``B`` when ``i`` is ``i0`` using
``e`` and ``B`` when ``i`` is ``i1`` using the identity
equivalence. This hence gives us the key part of univalence:
equivalences are paths. The other part of univalence is that this map
itself is an equivalence which follows from the computation rule for
ua:

.. code-block:: agda

  uaβ : ∀ {ℓ} {A B : Set ℓ} (e : A ≃ B) (x : A) → transport (ua e) x ≡ e .fst x
  uaβ e x = transportRefl (e .fst x)

Transporting along the path that we get from ua is the same as
applying the equivalence. For more results about Glue types and
univalence see Cubical.Primitives.Glue and
Cubical.Foundations.Univalence in the agda/cubical library.


Higher inductive types
----------------------

Cubical Agda also lets us directly define higher inductive types as
datatypes with path constructors. For example the circle and torus can
be defined as:

.. code-block:: agda

  data S¹ : Set where
    base : S¹
    loop : base ≡ base

  data Torus : Set where
    point : Torus
    line1 : point ≡ point
    line2 : point ≡ point
    square : PathP (λ i → line1 i ≡ line1 i) line2 line2

Functions out of higher inductive types can then be defined by
pattern-matching:

.. code-block:: agda

  t2c : Torus → S¹ × S¹
  t2c point        = ( base , base )
  t2c (line1 i)    = ( loop i , base )
  t2c (line2 j)    = ( base , loop j )
  t2c (square i j) = ( loop i , loop j )

  c2t : S¹ × S¹ → Torus
  c2t (base   , base)   = point
  c2t (loop i , base)   = line1 i
  c2t (base   , loop j) = line2 j
  c2t (loop i , loop j) = square i j

When giving the cases for the path and square constructors we have to
make sure that the function maps the boundary to the right things. For
instance if we would do:

.. code-block:: agda

  c2t' : S¹ × S¹ → Torus
  c2t' (base   , base)   = point
  c2t' (loop i , base)   = line2 i
  c2t' (base   , loop j) = line1 j
  c2t' (loop i , loop j) = square i j

then Agda will complain that something is not right (the boundary of
the last case does not match up with the expected boundary of the
square constructor).

These compute judgmentally:

.. code-block:: agda

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
that the Torus is equal to two circles:

.. code-block:: agda

  Torus≡S¹×S¹ : Torus ≡ S¹ × S¹
  Torus≡S¹×S¹ = isoToPath (iso t2c c2t t2c-c2t c2t-t2c)

Cubical Agda also supports parametrized and recursive HITs. For
example propositional truncation is defined as:

.. code-block:: agda

  data ∥_∥ {ℓ} (A : Set ℓ) : Set ℓ where
    ∣_∣ : A → ∥ A ∥
    squash : ∀ (x y : ∥ A ∥) → x ≡ y

  recPropTrunc : ∀ {ℓ} {A : Set ℓ} {P : Set ℓ} → isProp P → (A → P) → ∥ A ∥ → P
  recPropTrunc Pprop f ∣ x ∣          = f x
  recPropTrunc Pprop f (squash x y i) =
    Pprop (recPropTrunc Pprop f x) (recPropTrunc Pprop f y) i


Cubical identity types and computational HoTT/UF
------------------------------------------------

As mentioned above the computation rule for J does not hold
definitionally for path types. Cubical Agda fixes this by introducing
a Cubical Identity type. The Cubical.Core.Id file of agda/cubical
exports all of the primitives of this type, including the notation _≡_
and the J eliminator that computes definitionally on refl.

The Cubical Id type and the path type are equivalent, so all of the
results for one can be transported to the other. Using this we provide
an interface to HoTT/UF in Cubical.Core.HoTT-UF which provides the
user with all of the primitives of Homotopy Type Theory and Univalent
Foundations implemented using Cubical primitives under the hood. This
hence gives an axiom free version of HoTT/UF which computes properly.

One drawback of the Cubical Id types compared to the propositional
equality of Agda is that it is not possible to use pattern-matching
when writing functions on them. This will hopefully be fixed in a
future version of Agda, but for now one has to use the J eliminator
explicitly.


----------
References
----------

.. _`CCHM`:

  Cyril Cohen, Thierry Coquand, Simon Huber and Anders Mörtberg;
  `“Cubical Type Theory: a constructive interpretation of the
  univalence axiom” <https://arxiv.org/abs/1611.02108>`_.

.. _`CHM`:

  Thierry Coquand, Simon Huber, Anders Mörtberg; `"On Higher Inductive
  Types in Cubical Type Theory" <https://arxiv.org/abs/1802.01170>`_.
