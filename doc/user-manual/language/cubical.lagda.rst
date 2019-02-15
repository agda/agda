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
of `CCHM, Cubical`_ where the Kan composition operations are
decomposed into homogeneous composition and generalized
transport. This what makes a general schema for higher inductive types
work, following `CHM, Cubical`_.

To use cubical type theory, you need to run Agda with the
``--cubical`` command-line-option. You can also write ``{-#
OPTIONS --cubical #-}`` at the top of the file.

The cubical mode adds the following features to Agda:

1. An interval and path types
2. Partial elements and systems
3. Kan operations (hcomp and transp)
4. Glue types
5. Cubical identity types
6. Higher inductive types


There is a library for Cubical Agda available at:
https://github.com/agda/cubical

The main design choices of the core part of the library are explained
in: https://homotopytypetheory.org/2018/12/06/cubical-agda/

In order to use Cubical Agda one should either import
https://github.com/agda/cubical/blob/master/Cubical/Core/Primitives.agda
or add the relevant import statements from the top of that file.


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

A ``Path``` is in fact a special case of the more general built-in
heterogeneous path type:

.. code-block:: agda
                
   -- PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

   -- Non dependent path types
   Path : ∀ {ℓ} (A : Set ℓ) → A → A → Set ℓ
   Path A a b = PathP (λ _ → A) a b


Because of the intuitions that paths correspond to equality ``PathP (λ
i → A) x y`` gets printed as ``x ≡ y`` when ``A`` does not mention
``i``.

By mapping out of more elements of the interval we can define squares,
cubes, and higher cubes in Agda, making the type theory "cubical".

Viewing equalities as functions out of the interval makes it possible
to do a lot of equality reasoning in a very direct way:

  sym : ∀ {ℓ} {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym p = λ i → p (~ i)

  cong : ∀ {ℓ} {A : Set} {x y : A} {B : A → Set ℓ'}
           (f : (a : A) → B a) (p : x ≡ y)
         → PathP (λ i → B (p i)) (f x) (f y)
  cong f p = λ i → f (p i)

Because of the way functions compute these satisfy some new
definitional equalities:

  sym sym = id
  cong refl = refl
  cong (f o g) = cong f o cong g

that are not available in standard Agda. Furthermore, path types lets
us prove new things are not true provable in standard Agda, for
example function extensionality (pointwise equal functions are equal):

  funExt : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x} →
             ((x : A) → f x ≡ g x) → f ≡ g
  funExt p i x = p x i


Partial elements and systems
----------------------------



-- * @IsOne r@ represents the constraint "r = i1".
-- Often we will use "φ" for elements of I, when we intend to use them
-- with IsOne (or Partial[P]).
-- IsOne : I → Setω

-- i1 is indeed equal to i1.
-- 1=1 : IsOne i1


-- * Types of partial elements, and their dependent version.

-- "Partial φ A" is a special version of "IsOne φ → A" with a more
-- extensional judgmental equality.
-- "PartialP φ A" allows "A" to be defined only on "φ".

-- Partial : ∀ {ℓ} → I → Set ℓ → Setω
-- PartialP : ∀ {ℓ} → (φ : I) → Partial φ (Set ℓ) → Setω

-- Partial elements are introduced by pattern matching with (r = i0)
-- or (r = i1) constraints, like so:

private
  sys : ∀ i → Partial (i ∨ ~ i) Set₁
  sys i (i = i0) = Set
  sys i (i = i1) = Set → Set

  -- It also works with pattern matching lambdas:
  --  http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.PatternMatchingLambdas
  sys' : ∀ i → Partial (i ∨ ~ i) Set₁
  sys' i = λ { (i = i0) → Set
             ; (i = i1) → Set → Set
             }

  -- When the cases overlap they must agree.
  sys2 : ∀ i j → Partial (i ∨ (i ∧ j)) Set₁
  sys2 i j = λ { (i = i1)          → Set
               ; (i = i1) (j = i1) → Set
               }

  -- (i0 = i1) is actually absurd.
  sys3 : Partial i0 Set₁
  sys3 = λ { () }


-- * There are cubical subtypes as in CCHM. Note that these are not
-- fibrant (hence in Setω):

_[_↦_] : ∀ {ℓ} (A : Set ℓ) (φ : I) (u : Partial φ A) → Agda.Primitive.Setω
A [ φ ↦ u ] = Sub A φ u

infix 4 _[_↦_]

-- Any element u : A can be seen as an element of A [ φ ↦ u ] which
-- agrees with u on φ:

-- inc : ∀ {ℓ} {A : Set ℓ} {φ} (u : A) → A [ φ ↦ (λ _ → u) ]

-- One can also forget that an element agrees with u on φ:

ouc : ∀ {ℓ} {A : Set ℓ} {φ : I} {u : Partial φ A} → A [ φ ↦ u ] → A
ouc = primSubOut


Kan operations (hcomp and transp)
---------------------------------


-- * Generalized transport and homogeneous composition [CHM 18].

-- When calling "transp A φ a" Agda makes sure that "A" is constant on "φ".
-- transp : ∀ {ℓ} (A : I → Set ℓ) (φ : I) (a : A i0) → A i1

-- When calling "hcomp A φ u a" Agda makes sure that "a" agrees with "u i0" on "φ".
-- hcomp : ∀ {ℓ} {A : Set ℓ} {φ : I} (u : I → Partial φ A) (a : A) → A

private
  variable
    ℓ  : Level
    ℓ′ : I → Level

-- Homogeneous filling
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

-- Heterogeneous composition defined as in CHM
comp : (A : ∀ i → Set (ℓ′ i))
       {φ : I}
       (u : ∀ i → Partial φ (A i))
       (u0 : A i0 [ φ ↦ u i0 ])
     → ---------------------------
       A i1
comp A {φ = φ} u u0 =
  hcomp (λ i → λ { (φ = i1) → transp (λ j → A (i ∨ j)) i (u _ 1=1) })
        (transp A i0 (ouc u0))

-- Heterogeneous filling defined using comp
fill : (A : ∀ i → Set (ℓ′ i))
       {φ : I}
       (u : ∀ i → Partial φ (A i))
       (u0 : A i0 [ φ ↦ u i0 ])
       ---------------------------
       (i : I) → A i
fill A {φ = φ} u u0 i =
  comp (λ j → A (i ∧ j))
       (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                ; (i = i0) → ouc u0 })
       (inc {φ = φ ∨ (~ i)} (ouc {φ = φ} u0))

-- Direct definition of transport filler, note that we have to
-- explicitly tell Agda that the type is constant (like in CHM)
transpFill : {A : Set ℓ}
             (φ : I)
             (A : (i : I) → Set ℓ [ φ ↦ (λ _ → A) ])
             (u0 : ouc (A i0))
           → --------------------------------------
             PathP (λ i → ouc (A i)) u0 (transp (λ i → ouc (A i)) φ u0)
transpFill φ A u0 i = transp (λ j → ouc (A (i ∧ j))) (~ i ∨ φ) u0


Glue types
----------


open import Agda.Builtin.Cubical.Glue public
  using ( isEquiv       -- ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set (ℓ ⊔ ℓ')

        ; equiv-proof   -- ∀ (y : B) → isContr (fiber f y)

        ; _≃_           -- ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')

        ; equivFun      -- ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → A → B

        ; equivProof    -- ∀ {ℓ ℓ'} (T : Set ℓ) (A : Set ℓ') (w : T ≃ A) (a : A) φ →
                        -- Partial φ (fiber (equivFun w) a) → fiber (equivFun w) a

        ; primGlue      -- ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I} (T : Partial φ (Set ℓ'))
                        -- → (e : PartialP φ (λ o → T o ≃ A)) → Set ℓ'

        ; prim^unglue   -- ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I} {T : Partial φ (Set ℓ')}
                        -- → {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A

        -- The ∀ operation on I. This is commented out as it is not currently used for anything
        -- ; primFaceForall -- (I → I) → I
        )
  renaming ( prim^glue   to glue         -- ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I} {T : Partial φ (Set ℓ')}
                                         -- → {e : PartialP φ (λ o → T o ≃ A)}
                                         -- → PartialP φ T → A → primGlue A T e

           ; pathToEquiv to lineToEquiv  -- ∀ {ℓ : → Level} (P : (i : I) → Set (ℓ i)) → P i0 ≃ P i1
           )

private
  variable
    ℓ ℓ' : Level

fiber : ∀ {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

equivIsEquiv : ∀ {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) → isEquiv (equivFun e)
equivIsEquiv e = snd e

equivCtr : ∀ {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) (y : B) → fiber (equivFun e) y
equivCtr e y = e .snd .equiv-proof y .fst

equivCtrPath : ∀ {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) (y : B) →
  (v : fiber (equivFun e) y) → Path _ (equivCtr e y) v
equivCtrPath e y = e .snd .equiv-proof y .snd

-- Uncurry Glue to make it more pleasant to use
Glue : ∀ (A : Set ℓ) {φ : I}
       → (Te : Partial φ (Σ[ T ∈ Set ℓ' ] T ≃ A))
       → Set ℓ'
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

-- Make the φ argument of prim^unglue explicit
unglue : ∀ {A : Set ℓ} (φ : I) {T : Partial φ (Set ℓ')}
           {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A
unglue φ = prim^unglue {φ = φ}

-- The identity equivalence
idfun : ∀ {ℓ} → (A : Set ℓ) → A → A
idfun _ x = x

idIsEquiv : ∀ (A : Set ℓ) → isEquiv (idfun A)
equiv-proof (idIsEquiv A) y =
  ((y , refl) , λ z i → z .snd (~ i) , λ j → z .snd (~ i ∨ j))

idEquiv : ∀ (A : Set ℓ) → A ≃ A
idEquiv A = (idfun A , idIsEquiv A)

-- The ua constant
ua : ∀ {A B : Set ℓ} → A ≃ B → A ≡ B
ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                   ; (i = i1) → (B , idEquiv B) })


-- Proof of univalence using that unglue is an equivalence:

-- unglue is an equivalence
unglueIsEquiv : ∀ (A : Set ℓ) (φ : I)
                (f : PartialP φ (λ o → Σ[ T ∈ Set ℓ ] T ≃ A)) →
                isEquiv {A = Glue A f} (unglue φ)
equiv-proof (unglueIsEquiv A φ f) = λ (b : A) →
  let u : I → Partial φ A
      u i = λ{ (φ = i1) → equivCtr (f 1=1 .snd) b .snd (~ i) }
      ctr : fiber (unglue φ) b
      ctr = ( glue (λ { (φ = i1) → equivCtr (f 1=1 .snd) b .fst }) (hcomp u b)
            , λ j → hfill u (inc b) (~ j))
  in ( ctr
     , λ (v : fiber (unglue φ) b) i →
         let u' : I → Partial (φ ∨ ~ i ∨ i) A
             u' j = λ { (φ = i1) → equivCtrPath (f 1=1 .snd) b v i .snd (~ j)
                      ; (i = i0) → hfill u (inc b) j
                      ; (i = i1) → v .snd (~ j) }
         in ( glue (λ { (φ = i1) → equivCtrPath (f 1=1 .snd) b v i .fst }) (hcomp u' b)
            , λ j → hfill u' (inc b) (~ j)))

-- Any partial family of equivalences can be extended to a total one
-- from Glue [ φ ↦ (T,f) ] A to A
unglueEquiv : ∀ (A : Set ℓ) (φ : I)
              (f : PartialP φ (λ o → Σ[ T ∈ Set ℓ ] T ≃ A)) →
              (Glue A f) ≃ A
unglueEquiv A φ f = ( unglue φ , unglueIsEquiv A φ f )


-- The following is a formulation of univalence proposed by Martín Escardó:
-- https://groups.google.com/forum/#!msg/homotopytypetheory/HfCB_b-PNEU/Ibb48LvUMeUJ
-- See also Theorem 5.8.4 of the HoTT Book.
--
-- The reason we have this formulation in the core library and not the
-- standard one is that this one is more direct to prove using that
-- unglue is an equivalence. The standard formulation can be found in
-- Cubical/Basics/Univalence.
--
EquivContr : ∀ (A : Set ℓ) → isContr (Σ[ T ∈ Set ℓ ] T ≃ A)
EquivContr {ℓ = ℓ} A =
  ( ( A , idEquiv A)
  , λ w i → let f : PartialP (~ i ∨ i) (λ x → Σ[ T ∈ Set ℓ ] T ≃ A)
                f = λ { (i = i0) → A , idEquiv A ; (i = i1) → w }
            in ( Glue A f , unglueEquiv _ _ f) )


Cubical identity types
----------------------


open import Agda.Builtin.Cubical.Id public
  renaming ( conid to ⟨_,_⟩
           -- TODO: should the user really be able to access these two?
           ; primIdFace to faceId  -- ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → I
           ; primIdPath to pathId  -- ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → Path A x y

           ; primIdElim to elimId  -- ∀ {ℓ ℓ'} {A : Set ℓ} {x : A}
                                   -- (P : ∀ (y : A) → x ≡ y → Set ℓ')
                                   -- (h : ∀ (φ : I) (y : A [ φ ↦ (λ _ → x) ])
                                   --        (w : (Path _ x (ouc y)) [ φ ↦ (λ { (φ = i1) → λ _ → x}) ] ) →
                                   --        P (ouc y) ⟨ φ , ouc w ⟩) →
                                   -- {y : A} (w' : x ≡ y) → P y w'
           )

-- Version of the constructor for Id where the y is also
-- explicit. This is sometimes useful when it is needed for
-- typechecking (see JId below).
conId : ∀ {x : A} φ (y : A [ φ ↦ (λ _ → x) ])
          (w : (Path _ x (ouc y)) [ φ ↦ (λ { (φ = i1) → λ _ → x}) ]) →
          x ≡ ouc y
conId φ _ w = ⟨ φ , ouc w ⟩

-- Reflexivity
refl : ∀ {x : A} → x ≡ x
refl {x = x} = ⟨ i1 , (λ _ → x) ⟩


-- Definition of J for Id
module _ {x : A} (P : ∀ (y : A) → Id x y → Set ℓ') (d : P x refl) where
  J : ∀ {y : A} (w : x ≡ y) → P y w
  J {y = y} = elimId P (λ φ y w → comp (λ i → P _ (conId (φ ∨ ~ i) (inc (ouc w i))
                                                                   (inc (λ j → ouc w (i ∧ j)))))
                                       (λ i → λ { (φ = i1) → d}) (inc d)) {y = y}

  -- Check that J of refl is the identity function
  Jdefeq : Path _ (J refl) d
  Jdefeq _ = d


Higher inductive types
----------------------


data S¹ : Set where
  base : S¹
  loop : base ≡ base


  
data Torus : Set where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 i ≡ line1 i) line2 line2

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

Torus≡S¹×S¹ : Torus ≡ S¹ × S¹
Torus≡S¹×S¹ = isoToPath (iso t2c c2t t2c-c2t c2t-t2c)

ΩTorus : Set
ΩTorus = point ≡ point



data ∥_∥ {ℓ} (A : Set ℓ) : Set ℓ where
  ∣_∣ : A → ∥ A ∥
  squash : ∀ (x y : ∥ A ∥) → x ≡ y

private
  variable
    ℓ : Level
    A : Set ℓ

recPropTrunc : ∀ {P : Set ℓ} → isProp P → (A → P) → ∥ A ∥ → P
recPropTrunc Pprop f ∣ x ∣          = f x
recPropTrunc Pprop f (squash x y i) =
  Pprop (recPropTrunc Pprop f x) (recPropTrunc Pprop f y) i


----------
References
----------

.. _`CCHM, Cubical`:

  Cyril Cohen, Thierry Coquand, Simon Huber and Anders Mörtberg;
  `“Cubical Type Theory: a constructive interpretation of the
  univalence axiom” <https://arxiv.org/abs/1611.02108>`_.

.. _`CHM, Cubical`:

  Thierry Coquand, Simon Huber, Anders Mörtberg; `"On Higher Inductive
  Types in Cubical Type Theory" <https://arxiv.org/abs/1802.01170>`_.
