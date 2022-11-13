..
  ::
  module language.foreign-function-interface where

  open import Agda.Primitive
  open import Agda.Builtin.Bool

  postulate <Name> : Set

.. _foreign-function-interface:

**************************
Foreign Function Interface
**************************

.. contents::
   :depth: 2
   :local:

Compiler Pragmas
================

There are two backend-generic pragmas used for the FFI::

  {-# COMPILE <Backend> <Name> <Text> #-}
  {-# FOREIGN <Backend> <Text> #-}

The ``COMPILE`` pragma associates some information ``<Text>`` with a
name ``<Name>`` defined in the same module, and the ``FOREIGN`` pragma
associates ``<Text>`` with the current top-level module. This
information is interpreted by the specific backend during compilation
(see below). These pragmas were added in Agda 2.5.3.

Haskell FFI
===========

.. note::
   This section applies to the :ref:`ghc-backend`.

The ``FOREIGN`` pragma
----------------------

The GHC backend interprets ``FOREIGN`` pragmas as inline Haskell code and can
contain arbitrary code (including import statements) that will be added to the
compiled module. For instance::

  {-# FOREIGN GHC import Data.Maybe #-}

  {-# FOREIGN GHC
    data Foo = Foo | Bar Foo

    countBars :: Foo -> Integer
    countBars Foo = 0
    countBars (Bar f) = 1 + countBars f
  #-}

The ``COMPILE`` pragma
----------------------

There are four forms of ``COMPILE`` annotations recognized by the GHC backend

.. code-block:: agda

  {-# COMPILE GHC <Name> = <HaskellCode> #-}
  {-# COMPILE GHC <Name> = type <HaskellType> #-}
  {-# COMPILE GHC <Name> = data <HaskellData> (<HsCon1> | .. | <HsConN>) #-}
  {-# COMPILE GHC <Name> as <HaskellName> #-}

The first three tells the compiler how to compile a given Agda definition and the last
exposes an Agda definition under a particular Haskell name allowing Agda libraries to
be used from Haskell.

.. _compiled_type_pragma:

Using Haskell Types from Agda
-----------------------------

In order to use a Haskell function from Agda its type must be mapped to an Agda
type. This mapping can be configured using the ``type`` and ``data`` forms of the
``COMPILE`` pragma.

Opaque types
^^^^^^^^^^^^

Opaque Haskell types are exposed to Agda by postulating an Agda type and
associating it to the Haskell type using the ``type`` form of the ``COMPILE``
pragma::

  {-# FOREIGN GHC import qualified System.IO #-}

  postulate FileHandle : Set
  {-# COMPILE GHC FileHandle = type System.IO.Handle #-}

This tells the compiler that the Agda type ``FileHandle`` corresponds to the Haskell
type ``System.IO.Handle`` and will enable functions using file handles to be used
from Agda.

Data types
^^^^^^^^^^

Non-opaque Haskell data types can be mapped to Agda datatypes using the ``data`` form
of the ``COMPILED`` pragma::

  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just    : A → Maybe A

  {-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}

The compiler checks that the types of the Agda constructors match the types of the
corresponding Haskell constructors and that no constructors have been left out
(on either side).

Record types
^^^^^^^^^^^^

The ``data`` form of the ``COMPILE`` pragma also works with Agda's record types::

  import Agda.Builtin.List
  {-# FOREIGN GHC import Data.Tree #-}

  record Tree (A : Set) : Set where
    inductive
    constructor node
    field root-label : A
    field sub-forest : Agda.Builtin.List.List (Tree A)

  {-# COMPILE GHC Tree = data Tree (Node) #-}

Built-in Types
^^^^^^^^^^^^^^

The GHC backend compiles certain Agda :ref:`built-in types <built-ins>` to
special Haskell types. The mapping between Agda built-in types and Haskell
types is as follows:


=============  ==================
Agda Built-in  Haskell Type
=============  ==================
``NAT``        ``Integer``
``INTEGER``    ``Integer``
``STRING``     ``Data.Text.Text``
``CHAR``       ``Char``
``BOOL``       ``Bool``
``FLOAT``      ``Double``
=============  ==================

.. warning::
   Haskell code manipulating Agda natural numbers as integers must take
   care to avoid negative values.

.. warning::
   Agda ``FLOAT`` values have only one logical ``NaN`` value. At runtime,
   there might be multiple different ``NaN`` representations present. All
   such ``NaN`` values must be treated equal by FFI calls.

.. _compiled_pragma:

Using Haskell functions from Agda
---------------------------------

Once a suitable mapping between Haskell types and Agda types has been set
up, Haskell functions whose types map to Agda types can be exposed to Agda
code with a ``COMPILE`` pragma::

  open import Agda.Builtin.IO
  open import Agda.Builtin.String
  open import Agda.Builtin.Unit

  {-# FOREIGN GHC
    import qualified Data.Text.IO as Text
    import qualified System.IO as IO
  #-}

  postulate
    stdout    : FileHandle
    hPutStrLn : FileHandle → String → IO ⊤
  {-# COMPILE GHC stdout    = IO.stdout #-}
  {-# COMPILE GHC hPutStrLn = Text.hPutStrLn #-}

The compiler checks that the type of the given Haskell code matches the
type of the Agda function. Note that the ``COMPILE`` pragma only affects
the runtime behaviour--at type-checking time the functions are treated as
postulates.

.. warning::
   It is possible to give Haskell definitions to defined (non-postulate)
   Agda functions. In this case the Agda definition will be used at
   type-checking time and the Haskell definition at runtime. However, there
   are no checks to ensure that the Agda code and the Haskell code behave
   the same and **discrepancies may lead to undefined behaviour**.

   This feature can be used to let you reason about code involving calls to
   Haskell functions under the assumption that you have a correct Agda model
   of the behaviour of the Haskell code.

Using Agda functions from Haskell
---------------------------------

Since Agda 2.3.4 Agda functions can be exposed to Haskell code using
the ``as`` form of the ``COMPILE`` pragma::

  module IdAgda where

    idAgda : ∀ {A : Set} → A → A
    idAgda x = x

    {-# COMPILE GHC idAgda as idAgdaFromHs #-}

This tells the compiler that the Agda function ``idAgda`` should be compiled
to a Haskell function called ``idAgdaFromHs``. Without this pragma, functions
are compiled to Haskell functions with unpredictable names and, as a result,
cannot be invoked from Haskell. The type of ``idAgdaFromHs`` will be the translated
type of ``idAgda``.

The compiled and exported function ``idAgdaFromHs`` can then be imported and
invoked from Haskell like this:

.. code-block:: haskell

  -- file UseIdAgda.hs
  module UseIdAgda where

  import MAlonzo.Code.IdAgda (idAgdaFromHs)
  -- idAgdaFromHs :: () -> a -> a

  idAgdaApplied :: a -> a
  idAgdaApplied = idAgdaFromHs ()

Polymorphic functions
---------------------

Agda is a monomorphic language, so polymorphic functions are modeled
as functions taking types as arguments. These arguments will be
present in the compiled code as well, so when calling polymorphic
Haskell functions they have to be discarded explicitly. For instance,
::

  postulate
    ioReturn : {A : Set} → A → IO A

  {-# COMPILE GHC ioReturn = \ _ x -> return x #-}

In this case compiled calls to ``ioReturn`` will still have ``A`` as an
argument, so the compiled definition ignores its first argument
and then calls the polymorphic Haskell ``return`` function.

Level-polymorphic types
-----------------------

:ref:`Level-polymorphic types <universe-levels>` face a similar problem to
polymorphic functions. Since Haskell does not have universe levels the Agda
type will have more arguments than the corresponding Haskell type. This can be solved
by defining a Haskell type synonym with the appropriate number of phantom
arguments. For instance:

::

  data Either {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    left  : A → Either A B
    right : B → Either A B

  {-# FOREIGN GHC type AgdaEither a b = Either #-}
  {-# COMPILE GHC Either = data AgdaEither (Left | Right) #-}

Handling typeclass constraints
------------------------------

There is (currently) no way to map a Haskell type with type class constraints to an
Agda type. This means that functions with class constraints cannot be used from Agda.
However, this can be worked around by wrapping class constraints in Haskell data types,
and providing Haskell functions using explicit dictionary passing.

For instance, suppose we have a simple GUI library in Haskell:

.. code-block:: haskell

  module GUILib where
    class Widget w
    setVisible :: Widget w => w -> Bool -> IO ()

    data Window
    instance Widget Window
    newWindow :: IO Window

To use this library from Agda we first define a Haskell type for widget dictionaries and map this
to an Agda type ``Widget``::

  {-# FOREIGN GHC import GUILib #-}
  {-# FOREIGN GHC data WidgetDict w = Widget w => WidgetDict #-}

  postulate
    Widget : Set → Set
  {-# COMPILE GHC Widget = type WidgetDict #-}

We can then expose ``setVisible`` as an Agda function taking a Widget
:ref:`instance argument <instance-arguments>`::

  postulate
    setVisible : {w : Set} {{_ : Widget w}} → w → Bool → IO ⊤
  {-# COMPILE GHC setVisible = \ _ WidgetDict -> setVisible #-}

Note that the Agda ``Widget`` argument corresponds to a ``WidgetDict`` argument
on the Haskell side. When we match on the ``WidgetDict`` constructor in the Haskell
code, the packed up dictionary will become available for the call to ``setVisible``.

The window type and functions are mapped as expected and we also add an Agda instance
packing up the ``Widget Window`` Haskell instance into a ``WidgetDict``::

  postulate
    Window    : Set
    newWindow : IO Window
    instance WidgetWindow : Widget Window
  {-# COMPILE GHC Window       = type Window #-}
  {-# COMPILE GHC newWindow    = newWindow #-}
  {-# COMPILE GHC WidgetWindow = WidgetDict #-}

..
  ::
  infixr 1 _>>=_
  postulate
    return : {A : Set} → A → IO A
    _>>=_ : {A B : Set} → IO A → (A → IO B) → IO B
  {-# COMPILE GHC return = \ _ -> return #-}
  {-# COMPILE GHC _>>=_ = \ _ _ -> (>>=) #-}

We can then write code like this::

  openWindow : IO Window
  openWindow = newWindow         >>= λ w →
               setVisible w true >>= λ _ →
               return w

JavaScript FFI
==============

The :ref:`JavaScript backend <javascript-backend>` recognizes ``COMPILE`` pragmas of the following form::

  {-# COMPILE JS <Name> = <JsCode> #-}

where ``<Name>`` is a postulate, constructor, or data type. The code for a data type is used to compile
pattern matching and should be a function taking a value of the data type and a table of functions
(corresponding to case branches) indexed by the constructor names. For instance, this is the compiled
code for the ``List`` type, compiling lists to JavaScript arrays::

  data List {a} (A : Set a) : Set a where
    []  : List A
    _∷_ : (x : A) (xs : List A) → List A

  {-# COMPILE JS List = function(x,v) {
      if (x.length < 1) {
        return v["[]"]();
      } else {
        return v["_∷_"](x[0], x.slice(1));
      }
    } #-}
  {-# COMPILE JS []  = Array() #-}
  {-# COMPILE JS _∷_ = function (x) { return function(y) { return Array(x).concat(y); }; } #-}
