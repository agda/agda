..
  ::
  module language.lambda-abstraction where

  open import Agda.Primitive
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Equality

  record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field fst : A
          snd : B fst

.. _lambda-abstraction:

******************
Lambda Abstraction
******************

.. _pattern-lambda:

Pattern matching lambda
-----------------------

Anonymous pattern matching functions can be defined using one of the two
following syntaxes:

.. code-block:: agda

   \ { p11 .. p1n -> e1 ; … ; pm1 .. pmn -> em }

   \ where
     p11 .. p1n -> e1
     …
     pm1 .. pmn -> em

(where, as usual, ``\`` and ``->`` can be replaced by ``λ`` and ``→``).
Note that the ``where`` keyword introduces an *indented* block of clauses;
if there is only one clause then it may be used inline.

Internally this is translated into a function definition of the following form:

.. code-block:: agda

   extlam p11 .. p1n = e1
   …
   extlam pm1 .. pmn = em

where `extlam` is a fresh name. This means that anonymous pattern matching functions are generative. For instance, ``refl`` will not be accepted as an inhabitant of the type

..
  ::

  no-fun-ext : Set₀
  no-fun-ext =

::

    (λ { true → true ; false → false }) ==
    (λ { true → true ; false → false })

..
  ::
    where
      _==_ = _≡_ {A = Bool → Bool}

because this is equivalent to ``extlam1 ≡ extlam2`` for some distinct fresh names ``extlam1`` and ``extlam2``.
Currently the ``where`` and ``with`` constructions are not allowed in (the top-level clauses of) anonymous pattern matching functions.

Examples:

::

  and : Bool → Bool → Bool
  and = λ { true x → x ; false _ → false }

  xor : Bool → Bool → Bool
  xor = λ { true  true  → false
          ; false false → false
          ; _     _     → true
          }

  eq : Bool → Bool → Bool
  eq = λ where
    true  true  → true
    false false → true
    _ _ → false

  fst : {A : Set} {B : A → Set} → Σ A B → A
  fst = λ { (a , b) → a }

  snd : {A : Set} {B : A → Set} (p : Σ A B) → B (fst p)
  snd = λ { (a , b) → b }

  swap : {A B : Set} → Σ A (λ _ → B) → Σ B (λ _ → A)
  swap = λ where (a , b) → (b , a)
