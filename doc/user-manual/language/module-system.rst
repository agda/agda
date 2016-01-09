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

  data Nat : Set where
    zero : Nat
    suc  : Nat → Nat

  module B where
    f : Nat → Nat
    f n = suc n

  g : Nat → Nat → Nat
  g n m = m
Note that we use indentation to indicate which definitions are part of a module. In the example f is in the module Main.B and g is in Main. How to refer to a particular definition is determined by where it is located in the module hierarchy. Definitions from an enclosing module are referred to by their given names as seen in the type of f above. To access a definition from outside its defining module a qualified name has to be used.
::
 module Main where

   data Nat : Set where
     zero : Nat
     suc  : Nat → Nat

   module B where
     f : Nat → Nat
     f n = suc n

   ff : Nat → Nat
   ff x = B.f (B.f x)
To be able to use the short names for definitions in a module the module has to be opened.
::
 module Main where

   data Nat : Set where
     zero : Nat
     suc  : Nat → Nat

   module B where
     f : Nat → Nat
     f n = suc n

   open B

   ff : Nat → Nat
   ff x = f (f x)
If A.qname refers to a definition d then after open A, qname will also refer to d. Note that qname can itself be a qualified name. Opening a module only introduces new names for a definition, it never removes the old names. The policy is to allow the introduction of ambiguous names, but give an error if an ambiguous name is used.

Modules can also be opened within a local scope by putting the open B within a where clause:
::
  ff : Nat → Nat
  ff x = f (f x) where open B

Private definitions
-------------------
To make a definition inaccessible outside its defining module it can be declared private. A private definition is treated as a normal definition inside the module that defines it, but outside the module the definition has no name. In a dependently type setting there are some problems with private definitions---since the type checker performs computations, private names might show up in goals and error messages. Consider the following (contrived) example
::
 module Main where
  module A where

    private IsZero’ : Nat → Set
            IsZero’ Zero    = True
            IsZero’ (Suc n) = False

    IsZero : Nat → Set
    IsZero n = IsZero’ n

  open A
  prf : (n : Nat) → IsZero n
  prf n = ?0
The type of the goal ?0 is IsZero n which normalises to IsZero’ n. The question is how to display this normal form to the user. At the point of ?0 there is no name for IsZero’. One option could be try to fold the term and print IsZero n. This is a very hard problem in general, so rather than trying to do this we make it clear to the user that IsZero’ is something that is not in scope and print the goal as .Main.A.IsZero’ n. The leading dot indicates that the entity is not in scope. The same technique is used for definitions that only have ambiguous names.

In effect using private definitions means that from the user’s perspective we do not have subject reduction. This is just an illusion, however---the type checker has full access to all definitions.

Name modifiers
--------------
An alternative to making definitions private is to exert finer control over what names are introduced when opening a module. This is done by qualifying an open statement with one or more of the modifiers using, hiding, or renaming. You can combine both using and hiding with renaming, but not with each other. The effect of
::
  open A using (xs) renaming (ys to zs)
is to introduce the names xs and zs where xs refers to the same definition as A.xs and zs refers to A.ys. Note that if xs and ys overlap there will be two names introduced for the same definition. We do not permit xs and zs to overlap. The other forms of opening are defined in terms of this one. Let A denote all the (public) names in A. Then
::
  open A renaming (ys to zs)
  == open A hiding () renaming (ys to zs)

  open A hiding (xs) renaming (ys to zs)
  == open A using (A ; xs ; ys) renaming (ys to zs)
An omitted renaming modifier is equivalent to an empty renaming.

Re-exporting names
------------------
A useful feature is the ability to re-export names from another module. For instance, one may want to create a module to collect the definitions from several other modules. This is achieved by qualifying the open statement with the public keyword:
::
  module Example where

  module Nat where

    data Nat : Set where
      zero : Nat
      suc  : Nat → Nat

  module Bool where

    data Bool : Set where
      true false : Bool

  module Prelude where

    open Nat  public
    open Bool public

    isZero : Nat → Bool
    isZero zero    = true
    isZero (suc _) = false
The module Prelude above exports the names Nat, zero, Bool, etc., in addition to isZero.

Parameterised modules
---------------------
So far, the module system features discussed have dealt solely with scope manipulation. We now turn our attention to some more advanced features.

It is sometimes useful to be able to work temporarily in a given signature. For instance, when defining functions for sorting lists it is convenient to assume a set of list elements A and an ordering over A. In Coq this can be done in two ways: using a functor, which is essentially a function between modules, or using a section. A section allows you to abstract some arguments from several definitions at once. We introduce parameterised modules analogous to sections in Coq. When declaring a module you can give a telescope of module parameters which are abstracted from all the definitions in the module. For instance, a simple implementation of a sorting function looks like this:
::
 module Sort (A : Set)(_≤_ : A → A → Bool) where
   insert : A → List A → List A
   insert x  ε = x :: ε
   insert x (y :: ys) with x ≤ y
   insert x (y :: ys)    | true  = x :: y :: ys
   insert x (y :: ys)    | false = y :: insert x ys

   sort : List A → List A
   sort ε         = ε
   sort (x :: xs) = insert x (sort xs)
As mentioned parametrising a module has the effect of abstracting the parameters over the definitions in the module, so outside the Sort module we have
::
 Sort.insert : (A : Set)(_≤_ : A → A → Bool) →
               A → List A → List A
 Sort.sort   : (A : Set)(_≤_ : A → A → Bool) →
               List A → List A
For function definitions, explicit module parameter become explicit arguments to the abstracted function, and implicit parameters become implicit arguments. For constructors, however, the parameters are always implicit arguments. This is a consequence of the fact that module parameters are turned into datatype parameters, and the datatype parameters are implicit arguments to the constructors. It also happens to be the reasonable thing to do.

Something which you cannot do in Coq is to apply a section to its arguments. We allow this through the module application statement. In our example:
::
 module SortNat = Sort Nat leqNat
This will define a new module SortNat as follows
::
 module SortNat where
  insert : Nat → List Nat → List Nat
  insert = Sort.insert Nat leqNat

  sort : List Nat → List Nat
  sort = Sort.sort Nat leqNat
The new module can also be parameterised, and you can use name modifiers to control what definitions from the original module are applied and what names they have in the new module. The general form of a module application is
::
  module M1 Δ = M2 terms modifiers
A common pattern is to apply a module to its arguments and then open the resulting module. To simplify this we introduce the short-hand
::
  open module M1 Δ = M2 terms [public] mods
for
::
  module M1 Δ = M2 terms mods
  open M1 [public]

Splitting a program over multiple files
---------------------------------------
When building large programs it is crucial to be able to split the program over multiple files and to not have to type check and compile all the files for every change. The module system offers a structured way to do this. We define a program to be a collection of modules, each module being defined in a separate file. To gain access to a module defined in a different file you can import the module:
::
  import M
In order to implement this we must be able to find the file in which a module is defined. To do this we require that the top-level module A.B.C is defined in the file C.agda in the directory A/B/. One could imagine instead to give a file name to the import statement, but this would mean cluttering the program with details about the file system which is not very nice.

When importing a module M the module and its contents is brought into scope as if the module had been defined in the current file. In order to get access to the unqualified names of the module contents it has to be opened. Similarly to module application we introduce the short-hand
::
  open import M
for
::
  import M
  open M
Sometimes the name of an imported module clashes with a local module. In this case it is possible to import the module under a different name.
::
  import M as M’
It is also possible to attach modifiers to import statements, limiting or changing what names are visible from inside the module.

Datatype modules
----------------
When you define a datatype it also defines a module so constructors can now be referred to qualified by their data type.
For instance, given
::
    data Nat : Set where
        zero : Nat
        suc  : Nat → Nat

      data Fin : Nat → Set where
        zero : ∀ {n} → Fin (suc n)
        suc  : ∀ {n} → Fin n → Fin (suc n)
you can refer to the constructors unambiguously as Nat.zero, Nat.suc, Fin.zero, and Fin.suc (Nat and Fin are modules containing the respective constructors). Example:
::
      inj : (n m : Nat) → Nat.suc n ≡ suc m → n ≡ m
      inj .m m refl = refl
Previously you had to write something like
::
      inj : (n m : Nat) → _≡_ {Nat} (suc n) (suc m) → n ≡ m
to make the type checker able to figure out that you wanted the natural number suc in this case.

Record update syntax
--------------------
Assume that we have a record type and a corresponding value:
::
  record MyRecord : Set where
    field
      a b c : ℕ

  old : MyRecord
  old = record { a = 1; b = 2; c = 3 }
Then we can update (some of) the record value’s fields in the following way:
::
  new : MyRecord
  new = record old { a = 0; c = 5 }
Here new normalises to record { a = 0; b = 2; c = 5 }. Any expression yielding a value of type MyRecord can be used instead of old.

Record updating is not allowed to change types: the resulting value must have the same type as the original one, including the record parameters. Thus, the type of a record update can be inferred if the type of the original record can be inferred.

The record update syntax is expanded before type checking. When the expression
::
  record old { upd-fields }
is checked against a record type R, it is expanded to
::
  let r = old in record { new-fields },
where old is required to have type R and new-fields is defined as follows: for each field x in R,
  - if x = e is contained in upd-fields then x = e is included in
    new-fields, and otherwise
  - if x is an explicit field then x = R.x r is included in
    new-fields, and
  - if x is an implicit or instance field, then it is omitted from
    new-fields.
(Instance arguments are explained below.) The reason for treating implicit and instance fields specially is to allow code like the following:
::
  record R : Set where
    field
      {length} : ℕ
      vec      : Vec ℕ length
      — More fields…

  xs : R
  xs = record { vec = 0 ∷ 1 ∷ 2 ∷ [] }

  ys = record xs { vec = 0 ∷ [] }
Without the special treatment the last expression would need to include a new binding for length (for instance “length = _”).
