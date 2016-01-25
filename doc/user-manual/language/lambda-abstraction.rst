.. _lambda-abstraction:

******************
Lambda Abstraction
******************

.. _pattern-lambda:

Pattern matching lambda
-----------------------

Anonymous pattern matching functions can be defined using the syntax::

   \ { p11 .. p1n -> e1 ; … ; pm1 .. pmn -> em }

(where, as usual, ``\`` and ``->`` can be replaced by ``λ`` and ``→``). Internally this is translated into a function definition of the following form:::

   .extlam p11 .. p1n = e1
   …
   .extlam pm1 .. pmn = em

This means that anonymous pattern matching functions are generative. For instance, ``refl`` will not be accepted as an inhabitant of the type::

   (λ { true → true ; false → false }) ≡
   (λ { true → true ; false → false }),

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

   fst : {A : Set} {B : A → Set} → Σ A B → A
   fst = λ { (a , b) → a }

   snd : {A : Set} {B : A → Set} (p : Σ A B) → B (fst p)
   snd = λ { (a , b) → b }
