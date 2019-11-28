..
  ::
  {-# OPTIONS --allow-unsolved-metas #-}
  module language.module-system where

  open import language.built-ins

.. _module-system:

*************
Module System
*************

.. _module-application:

Module application
------------------

.. _anonymous-modules:

Anonymous modules
-----------------

Basics
------
First let us introduce some terminology. A definition is a syntactic construction defining an entity such as a function or a datatype. A name is a string used to identify definitions. The same definition can have many names and at different points in the program it will have different names. It may also be the case that two definitions have the same name. In this case there will be an error if the name is used.

The main purpose of the module system is to structure the way names are used in a program. This is done by organising the program in an hierarchical structure of modules where each module contains a number of definitions and submodules. For instance,
::

  module Main where

    module B where
      f : Nat → Nat
      f n = suc n

    g : Nat → Nat → Nat
    g n m = m

Note that we use indentation to indicate which definitions are part of a module. In the example ``f`` is in the module ``Main.B`` and ``g`` is in ``Main``. How to refer to a particular definition is determined by where it is located in the module hierarchy. Definitions from an enclosing module are referred to by their given names as seen in the type of f above. To access a definition from outside its defining module a qualified name has to be used.
::

  module Main₂ where

    module B where
      f : Nat → Nat
      f n = suc n

    ff : Nat → Nat
    ff x = B.f (B.f x)

To be able to use the short names for definitions in a module the module has to be opened.
::

  module Main₃ where

    module B where
      f : Nat → Nat
      f n = suc n

    open B

    ff : Nat → Nat
    ff x = f (f x)

If ``A.qname`` refers to a definition ``d``, then after ``open A``, ``qname`` will also refer to ``d``. Note that ``qname`` can itself be a qualified name. Opening a module only introduces new names for a definition, it never removes the old names. The policy is to allow the introduction of ambiguous names, but give an error if an ambiguous name is used.

Modules can also be opened within a local scope by putting the ``open B`` within a ``where`` clause:
::

    ff₁ : Nat → Nat
    ff₁ x = f (f x) where open B

Private definitions
-------------------
To make a definition inaccessible outside its defining module it can be declared ``private``. A private definition is treated as a normal definition inside the module that defines it, but outside the module the definition has no name. In a dependently type setting there are some problems with private definitions---since the type checker performs computations, private names might show up in goals and error messages. Consider the following (contrived) example
::

  module Main₄ where
    module A where

      private
        IsZero’ : Nat → Set
        IsZero’ zero    = ⊤
        IsZero’ (suc n) = ⊥

      IsZero : Nat → Set
      IsZero n = IsZero’ n

    open A
    prf : (n : Nat) → IsZero n
    prf n = ?

The type of the goal ``?0`` is ``IsZero n`` which normalises to ``IsZero’ n``. The question is how to display this normal form to the user. At the point of ``?0`` there is no name for ``IsZero’``. One option could be try to fold the term and print ``IsZero n``. This is a very hard problem in general, so rather than trying to do this we make it clear to the user that ``IsZero’`` is something that is not in scope and print the goal as ``;Main₄.A.IsZero’ n``. The leading semicolon indicates that the entity is not in scope. The same technique is used for definitions that only have ambiguous names.

In effect using private definitions means that, from the user’s perspective, we do not have subject reduction. This is just an illusion, however---the type checker has full access to all definitions.

Name modifiers
--------------
An alternative to making definitions private is to exert finer control over what names are introduced when opening a module. This is done by qualifying an ``open`` statement with one or more of the modifiers ``using``, ``hiding``, or ``renaming``. You can combine both ``using`` and ``hiding`` with ``renaming``, but not with each other. The effect of

.. code-block:: agda

  open A using (xs) renaming (ys to zs)

is to introduce the names ``xs`` and ``zs`` where ``xs`` refers to the same definition as ``A.xs`` and ``zs`` refers to ``A.ys``. We do not permit ``xs``, ``ys`` and ``zs`` to overlap. The other forms of opening are defined in terms of this one.
An omitted ``renaming`` modifier is equivalent to an empty renaming.

To refer to a module ``M`` inside ``A`` you write ``module M``. For instance,

.. code-block:: agda

  open A using (module M)

Since 2.6.1: The fixity of an operator can be set or changed in a ``renaming`` directive::

  module ExampleRenamingFixity where

    module ArithFoo where
      postulate
        A : Set
        _&_ _^_ : A → A → A
      infixr 10 _&_

    open ArithFoo renaming (_&_ to infixl 8 _+_; _^_ to infixl 10 _^_)

Here, we change the fixity of ``_&_`` while renaming it to ``_+_``, and assign a new fixity to ``_^_`` which has the default fixity in module ``ArithFoo``.

Re-exporting names
------------------
A useful feature is the ability to re-export names from another module. For instance, one may want to create a module to collect the definitions from several other modules. This is achieved by qualifying the open statement with the public keyword:
::

  module Example where

    module Nat₁ where

      data Nat₁ : Set where
        zero : Nat₁
        suc  : Nat₁ → Nat₁

    module Bool₁ where

      data Bool₁ : Set where
        true false : Bool₁

    module Prelude where

      open Nat₁  public
      open Bool₁ public

      isZero : Nat₁ → Bool₁
      isZero zero    = true
      isZero (suc _) = false

The module ``Prelude`` above exports the names ``Nat``, ``zero``, ``Bool``, etc., in addition to ``isZero``.

Parameterised modules
---------------------
So far, the module system features discussed have dealt solely with scope manipulation. We now turn our attention to some more advanced features.

It is sometimes useful to be able to work temporarily in a given signature. For instance, when defining functions for sorting lists it is convenient to assume a set of list elements ``A`` and an ordering over ``A``. In Coq this can be done in two ways: using a functor, which is essentially a function between modules, or using a section. A section allows you to abstract some arguments from several definitions at once. We introduce parameterised modules analogous to sections in Coq. When declaring a module you can give a telescope of module parameters which are abstracted from all the definitions in the module. For instance, a simple implementation of a sorting function looks like this:
::

  module Sort (A : Set)(_≤_ : A → A → Bool) where
    insert : A → List A → List A
    insert x [] = x ∷ []
    insert x (y ∷ ys) with x ≤ y
    insert x (y ∷ ys)    | true  = x ∷ y ∷ ys
    insert x (y ∷ ys)    | false = y ∷ insert x ys

    sort : List A → List A
    sort []       = []
    sort (x ∷ xs) = insert x (sort xs)

As mentioned parametrising a module has the effect of abstracting the parameters over the definitions in the module, so outside the Sort module we have

.. code-block:: agda

  Sort.insert : (A : Set)(_≤_ : A → A → Bool) →
                 A → List A → List A
  Sort.sort   : (A : Set)(_≤_ : A → A → Bool) →
                 List A → List A

For function definitions, explicit module parameter become explicit arguments to the abstracted function, and implicit parameters become implicit arguments. For constructors, however, the parameters are always implicit arguments. This is a consequence of the fact that module parameters are turned into datatype parameters, and the datatype parameters are implicit arguments to the constructors. It also happens to be the reasonable thing to do.

Something which you cannot do in Coq is to apply a section to its arguments. We allow this through the module application statement. In our example:

.. code-block:: agda

  module SortNat = Sort Nat leqNat

This will define a new module SortNat as follows

.. code-block:: agda

  module SortNat where
    insert : Nat → List Nat → List Nat
    insert = Sort.insert Nat leqNat

    sort : List Nat → List Nat
    sort = Sort.sort Nat leqNat

The new module can also be parameterised, and you can use name modifiers to control what definitions from the original module are applied and what names they have in the new module. The general form of a module application is

.. code-block:: agda

  module M1 Δ = M2 terms modifiers

A common pattern is to apply a module to its arguments and then open the resulting module. To simplify this we introduce the short-hand

.. code-block:: agda

  open module M1 Δ = M2 terms [public] mods

for

.. code-block:: agda

  module M1 Δ = M2 terms mods
  open M1 [public]

Splitting a program over multiple files
---------------------------------------
When building large programs it is crucial to be able to split the program over multiple files and to not have to type check and compile all the files for every change. The module system offers a structured way to do this. We define a program to be a collection of modules, each module being defined in a separate file. To gain access to a module defined in a different file you can import the module:

.. code-block:: agda

  import M

In order to implement this we must be able to find the file in which a module is defined. To do this we require that the top-level module ``A.B.C`` is defined in the file ``C.agda`` in the directory ``A/B/``. One could imagine instead to give a file name to the import statement, but this would mean cluttering the program with details about the file system which is not very nice.

When importing a module ``M``, the module and its contents are brought into scope as if the module had been defined in the current file. In order to get access to the unqualified names of the module contents it has to be opened. Similarly to module application we introduce the short-hand

.. code-block:: agda

  open import M

for

.. code-block:: agda

  import M
  open M

Sometimes the name of an imported module clashes with a local module. In this case it is possible to import the module under a different name.

.. code-block:: agda

  import M as M’

It is also possible to attach modifiers to import statements, limiting or changing what names are visible from inside the module.
Note that modifiers attached to ``open import`` statements apply to the ``open`` statement and not the ``import`` statement.

Datatype modules and record modules
-----------------------------------
When you define a datatype it also defines a module so constructors can now be referred to qualified by their data type.
For instance, given::

  module DatatypeModules where

    data Nat₂ : Set where
      zero : Nat₂
      suc  : Nat₂ → Nat₂

    data Fin : Nat₂ → Set where
      zero : ∀ {n} → Fin (suc n)
      suc  : ∀ {n} → Fin n → Fin (suc n)

you can refer to the constructors unambiguously as ``Nat₂.zero``, ``Nat₂.suc``, ``Fin.zero``, and ``Fin.suc`` (``Nat₂`` and ``Fin`` are modules containing the respective constructors). Example:
::

    inj : (n m : Nat₂) → Nat₂.suc n ≡ suc m → n ≡ m
    inj .m m refl = refl

Previously you had to write something like
::

    inj₁ : (n m : Nat₂) → _≡_ {A = Nat₂} (suc n) (suc m) → n ≡ m
    inj₁ .m m refl = refl

to make the type checker able to figure out that you wanted the natural number suc in this case.

Also record declarations define a corresponding module, see
:ref:`record-modules`.
