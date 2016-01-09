.. _mutual-recursion:

****************
Mutual Recursion
****************

.. note::
   This is a stub.

It is no longer necessary to use the mutual keyword to define mutually recursive functions or datatypes. Instead, it is enough to declare things before they are used. Instead of
::
  mutual
    f : A
    f = a[f, g]

    g : B[f]
    g = b[f, g]
you can now write
::
  f : A
  g : B[f]
  f = a[f, g]
  g = b[f, g].
With the new style you have more freedom in choosing the order in which things are type checked (previously type signatures were always checked before definitions). Furthermore you can mix arbitrary declarations, such as modules and postulates, with mutually recursive definitions.
For data types and records the following new syntax is used to separate the declaration from the definition:
::
  — Declaration.
  data Vec (A : Set) : Nat → Set  — Note the absence of ‘where’.

  — Definition.
  data Vec A where
    []   : Vec A zero
    _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

  — Declaration.
  record Sigma (A : Set) (B : A → Set) : Set

  — Definition.
  record Sigma A B where
    constructor _,_
    field fst : A
          snd : B fst
When making separated declarations/definitions private or abstract you should attach the ‘private’ keyword to the declaration and the abstract keyword to the definition. For instance, a private, abstract function can be defined as
::
  private
    f : A
  abstract
    f = e
Finally it may be worth noting that the old style of mutually recursive definitions is still supported (it basically desugars into the new style).
