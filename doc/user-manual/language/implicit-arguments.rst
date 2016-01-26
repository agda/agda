.. _implicit-arguments:

******************
Implicit Arguments
******************

It is possible to omit terms that the type checker can figure out for itself, replacing them by _. If the type checker cannot infer the value of an _ it will report an error. For instance, for the polymorphic identity function
::

 id : (A : Set) → A → A

the first argument can be inferred from the type of the second argument, so we might write id _ zero for the application of the identity function to zero.

We can even write this function application without the first argument. In that case we declare an implicit function space:
::

 id : {A : Set} → A → A

and then we can use the notation id zero.

Another example:
::

 _==_  : {A : Set} → A → A → Set
 subst : {A : Set}(C : A → Set){x y : A} → x == y → C x → C y

Note how the first argument to _==_ is left implicit. Similarly we may leave out the implicit arguments A, x, and y in an application of subst. To give an implicit argument explicitly, enclose in curly braces. The following two expressions are equivalent:
::

 subst C eq cx
 subst {_} C {_} {_} eq cx

It is worth noting that implicit arguments are also inserted at the end of an application, if it is required by the type. For example, in the following, y1 and y2 are equivalent.
::

 y1 : a == b → C a → C b
 y1 = subst C

 y2 : a == b → C a → C b
 y2 = subst C {_} {_}

When no type signature is given, the implicit arguments are not applied; thus, y3 and y4 are also equivalent to each other (but not to y1 and y2).
::

 y3 : {x y : A} → x == y → C x → C y
 y3 = subst C

 y4 = subst C

Finally, less intuitively, y5 is also possible and equivalent to y3 and y4.
::

 y5 : {x y : A} → x == y → C x → C y
 y5 = subst C {_} {_}

It is also possible to write lambda abstractions with implicit arguments. For example, given id : (A : Set) → A → A, we can define the identity function with implicit type argument as
::

 id’ = \ { A } → id A

Implicit arguments can also be referred to by name, so if we want to give the expression e explicitly for y without giving a value for x we can write
::

  subst C {y = e} eq cx

When constructing implicit function spaces the implicit argument can be omitted, so both expressions below are valid expressions of type {A : Set} → A → A:
::

  \ { A } x → x
  \ x → x

The forall syntax for function types also has implicit variants:
::

 forall {x : A} → B    is the same as  {x : A} → B
 forall {x} → B        is the same as  {x : _} → B
 forall {x y} → B      is the same as  forall {x} → forall {y} → B

There are no restrictions on when a function space can be implicit. Internally, explicit and implicit function spaces are treated in the same way. This means that there are no guarantees that implicit arguments will be solved. When there are unsolved implicit arguments the type checker will give an error message indicating which application contains the unsolved arguments. The reason for this liberal approach to implicit arguments is that limiting the use of implicit argument to the cases where we guarantee that they are solved rules out many useful cases in practice.

.. _metavariables:

Metavariables
-------------

.. _unification:

Unification
-----------

