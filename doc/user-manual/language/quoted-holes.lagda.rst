.. _quoted-holes:

************
Quoted Holes
************

The option :option:`--quoted-holes` enables term quotation constraints to be resolved even when the term has meta variables in it. This allows for typed hole-driven development for macros, where the expected type for an interactive hole given as a quoted argument to a macro can be constrained by the unquoting of the macro.

Example
~~~~~~~

In the following example without, :option:`--quoted-holes` , the interactive hole will cause the constraint to be blocked, which looks something like ``quoteTerm ?0 : Term (blocked on _17)``.

.. code-block:: agda

    open import Agda.Builtin.Reflection
    open import Data.Unit.Base
    open import Data.Nat.Base
    open import Data.List.Base

    repeat-helper : ℕ → Name → Term → Term
    repeat-helper zero f a = a
    repeat-helper (suc n) f a = def f ((arg (arg-info visible (modality relevant quantity-ω)) (repeat-helper n f a)) ∷ [])

    macro
        repeat : ℕ → Name → Term → Term → TC ⊤
        repeat n f a hole = unify hole (repeat-helper n f a)

    f : ℕ → ℕ
    f = suc

    ex1 = repeat 10 f {! !}


However, actually unquoting the macro would reveal that the interactive hole should have type ``ℕ``. Enabling :option:`--quoted-holes` allows exactly this. 

.. code-block:: agda
    
    {-# OPTIONS --quoted-holes #-}

    -- ...

    ex1 = repeat 10 f {! !}

Now, the macro will be unquoted, which in this spliced code applies ``f`` to the hole's value. This constrains hole's type to be ``ℕ``, and the user can inspect the expected context and type of the hole to learn this.

.. note::

    In this example, the hole's type is not constrained by the spliced code, so it will have an unknown inferred type.

    .. code-block:: agda

        ex2 = repeat 0 f {! !}
