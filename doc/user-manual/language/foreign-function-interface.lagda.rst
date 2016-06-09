..
  ::
  module language.foreign-function-interface where

.. _foreign-function-interface:

**************************
Foreign Function Interface
**************************

Haskell FFI
===========

.. note::
   This section currently only applies
   to the GHC backend.

The FFI is controlled by five pragmas:

- ``IMPORT``
- ``COMPILED_TYPE``
- ``COMPILED_DATA``
- ``COMPILED``
- ``COMPILED_EXPORT``

All FFI bindings are only used when executing programs and do not influence the type checking phase.

The IMPORT pragma
-----------------

::

  {-# IMPORT HsModule #-}

The ``IMPORT`` pragma instructs the compiler to generate a Haskell import statement in the compiled code. The pragma above will generate the following Haskell code:

.. code-block:: haskell

  import qualified HsModule

``IMPORT`` pragmas can appear anywhere in a file.

The COMPILED_TYPE pragma
------------------------

::

  postulate D : Set
  {-# COMPILED_TYPE D HsType #-}

The ``COMPILED_TYPE`` pragma tells the compiler that the postulated Agda type ``D`` corresponds to the Haskell type ``HsType``. This information is used when checking the types of ``COMPILED`` functions and constructors.

The COMPILED_DATA pragma
------------------------

.. code-block:: agda

  {-# COMPILED_DATA D HsD HsC1 .. HsCn #-}

The ``COMPILED_DATA`` pragma tells the compiler that the Agda datatype ``D`` corresponds to the Haskell datatype ``HsD`` and that its constructors should be compiled to the Haskell constructors ``HsC1 .. HsCn``. The compiler checks that the Haskell constructors have the right types and that all constructors are covered.

Example:
::

  data List (A : Set) : Set where
    []   : List A
    _::_ : A → List A → List A

  {-# COMPILED_DATA List [] [] (:) #-}

Built-in Types
^^^^^^^^^^^^^^

The GHC backend compiles certain Agda built-ins to special Haskell
types. The mapping between Agda built-in types and Haskell types
is as follows:

+-------------------+-----------------------+
| Agda Built-in     | Haskell Type          |
+===================+=======================+
| ``STRING``        | ``Data.Text.Text``    |
+-------------------+-----------------------+
| ``CHAR``          | ``Char``              |
+-------------------+-----------------------+
| ``INTEGER``       | ``Integer``           |
+-------------------+-----------------------+
| ``BOOL``          | ``Boolean``           |
+-------------------+-----------------------+

The COMPILED pragma
-------------------

::

  postulate f : ∀ a b → (a → b) → List a → List b
  {-# COMPILED f HsCode #-}

The ``COMPILED`` pragma tells the compiler to compile the postulated function ``f`` to the Haskell Code ``HsCode``. ``HsCode`` can be an arbitrary Haskell term of the right type. This is checked by translating the given Agda type of ``f`` into a Haskell type (see :ref:`translating-agda-types-to-haskell`) and checking that this matches the type of ``HsCode``.

Example:
::

  postulate String : Set
  {-# BUILTIN STRING String #-}

  data Unit : Set where unit : Unit
  {-# COMPILED_DATA Unit () () #-}

  postulate
    IO       : Set → Set
    putStrLn : String → IO Unit

  {-# COMPILED_TYPE IO IO #-}
  {-# COMPILED putStrLn putStrLn #-}

Polymorphic functions
---------------------

Agda is a monomorphic language, so polymorphic functions are modeled as functions taking types as arguments. These arguments will be present in the compiled code as well, so when calling polymorphic Haskell functions they have to be discarded explicitly. For instance,
::

  postulate
    map : {A B : Set} → (A → B) → List A → List B

  {-# COMPILED map (\_ _ → map) #-}

In this case compiled calls to map will still have ``A`` and ``B`` as arguments, so the compiled definition ignores its two first arguments and then calls the polymorphic Haskell ``map`` function.

Handling typeclass constraints
------------------------------

The problem here is that Agda’s Haskell FFI doesn’t understand Haskell’s class system. If you look at this error message, GHC complains about a missing class constraint:

.. code-block:: text

  No instance for (Graphics.UI.Gtk.ObjectClass xA)
    arising from a use of Graphics.UI.Gtk.objectDestroy’

A work around to represent Haskell Classes in Agda is to use a Haskell datatype to represent the class constraint in a way Agda understands:

.. code-block:: haskell

  {-# LANGUAGE GADTs #-}
  data MyObjectClass a = ObjectClass a => Witness

We also need to write a small wrapper for the ``objectDestroy`` function in Haskell:

.. code-block:: haskell

  myObjectDestroy :: MyObjectClass a -> Signal a (IO ())
  myObjectDestroy Witness = objectDestroy

Notice that the class constraint disappeared from the Haskell type signature! The only missing part are the Agda FFI bindings:

::

  postulate
    Window : Set
    Signal : Set → Set → Set
    MyObjectClass : Set → Set
    windowInstance : MyObjectClass Window
    myObjectDestroy : ∀ {a} → MyObjectClass a → Signal a Unit
  {-# COMPILED_TYPE Window Window #-}
  {-# COMPILED_TYPE Signal Signal #-}
  {-# COMPILED_TYPE MyObjectClass MyObjectClass #-}
  {-# COMPILED windowInstance (Witness :: MyObjectClass Window) #-}
  {-# COMPILED myObjectDestroy (\_ → myObjectDestroy) #-}

Then you should be able to call this as follows in Agda::

  p : Signal Window Unit
  p = myObjectDestroy windowInstance

This is somewhat similar to doing a dictionary-translation of the Haskell class system and generates quite a bit of boilerplate code.

The COMPILED_EXPORT pragma
--------------------------
.. versionadded:: 2.3.4

::

  g : ∀ {a : Set} → a → a
  g x = x

  {-# COMPILED_EXPORT g hsNameForG #-}

The ``COMPILED_EXPORT`` pragma tells the compiler that the Agda function ``f`` should be compiled to a Haskell function called ``hsNameForF``. Without this pragma, functions are compiled to Haskell functions with unpredictable names and, as a result, cannot be invoked from Haskell. The type of ``hsNameForF`` will be the translated type of ``f`` (see :ref:`translating-agda-types-to-haskell`). If f is defined in file A/B.agda, then ``hsNameForF`` should be imported from module ``MAlonzo.Code.A.B``.

Example:
::

  -- file IdAgda.agda
  module IdAgda where

  idAgda : {A : Set} → A → A
  idAgda x = x

  {-# COMPILED_EXPORT idAgda idAgda #-}

The compiled and exported function ``idAgda`` can then be imported and invoked from Haskell like this:

.. code-block:: haskell

  -- file UseIdAgda.hs
  module UseIdAgda where

  import MAlonzo.Code.IdAgda (idAgda)
  -- idAgda :: () -> a -> a

  idAgdaApplied :: a -> a
  idAgdaApplied = idAgda ()


.. _translating-agda-types-to-haskell:

Translating Agda types to Haskell
---------------------------------

.. note::
   This section may contain outdated material!

When checking the type of COMPILED function f : A, the Agda type A is translated to a Haskell type TA and the Haskell code Ef is checked against this type. The core of the translation on kinds K[[M]], types T[[M]] and expressions E[[M]] is:

.. code-block:: text

    K[[ Set A ]] = *
    K[[ x As ]] = undef
    K[[ fn (x : A) B ]] = undef
    K[[ Pi (x : A) B ]] = K[[ A ]] ->  K[[ B ]]
    K[[ k As ]] =
      if COMPILED_TYPE k
      then *
      else undef

    T[[ Set A ]] = Unit
    T[[ x As ]] = x T[[ As ]]
    T[[ fn (x : A) B ]] = undef
    T[[ Pi (x : A) B ]] =
      if x in fv B
      then forall x . T[[ A ]] -> T[[ B ]]
      else T[[ A ]] -> T[[ B ]]
    T[[ k As ]] =
      if COMPILED_TYPE k T
      then T T[[ As ]]
      else if COMPILED k E
      then Unit
      else undef

    E[[ Set A ]] = unit
    E[[ x As ]] = x E[[ As ]]
    E[[ fn (x : A) B ]] = fn x . E[[ B ]]
    E[[ Pi (x : A) B ]] = unit
    E[[ k As ]] =
      if COMPILED k E
      then E E[[ As ]]
      else runtime-error

The T[[ Pi (x : A) B ]] case is worth mentioning. Since the compiler doesn’t erase type arguments we can’t translate (a : Set) → B to forall a. B — an argument of type Set will still be passed to a function of this type. Therefore, the translated type is forall a. () → B where the type argument is assumed to have unit type. This is safe since we will never actually look at the argument, and the compiler compiles types to ().
