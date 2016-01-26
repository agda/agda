.. _mixfix-operators:

****************
Mixfix Operators
****************

A name containing one or more name parts and one or more ``_`` can be used as an operator where the arguments go in place of the ``_``. For instance, an application of the name ``if_then_else_`` to arguments ``x``, ``y``, and ``z`` can be written either as a normal application ``if_then_else_ x y z`` or as an operator application ``if x then y else z``.

Examples:
::

  _and_ : Bool → Bool → Bool
  true and x = x
  false and _ = false
  if_then_else_ : {A : Set} → Bool → A → A → A
  if true then x else y = x
  if false then x else y = y
