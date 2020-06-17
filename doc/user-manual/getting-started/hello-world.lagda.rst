
..
  ::
  module getting-started.hello-world where

*********************
'Hello world' in Agda
*********************

This section's objective is providing the first glimpse of Agda with some
minimal examples. The first one is a demonstration of dependently typed
programming, and the second shows how to write proofs in Agda. Finally, we
will build a program that creates a GHC or Javascript executable.

Before proceeding, make sure that you :ref:`installed Agda <installation>`
and the `standard library
<https://github.com/agda/agda-stdlib/blob/master/notes/installation-guide.md>`_.
You will also need an editor with *interactive* capabilities, currently
Emacs via the :ref:`Emacs mode <emacs-mode>`, Atom via the
`agda mode for Atom <agda-mode_>`_ and VSCode via the
`agda mode for VSCode <vs-code_>`_ are supported.

.. _agda-mode: https://github.com/banacorn/agda-mode
.. _vs-code: https://github.com/banacorn/agda-mode-vscode

.. hint:: If you want a sneak peek of Agda without installing it, try the
  `Agda Pad <agda-pad_>`_

.. _agda-pad: https://agdapad.quasicoherent.io/

‘Hello world’ dependent type
============================

We will model the notion of vector space with Agda. Roughly speaking, a vector
is a list of objects with a determined length.

.. code-block:: agda

  module hello-world-dep where

  open import Agda.Builtin.Nat using (Nat ; zero ; suc)

  data Vec (A : Set) : ℕ → Set where
    []  : Vec A zero
    _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

  infixr 5 _∷_

This code has 6 declarations:

1. top level module declaration
2. imports of the declarations of the datatype ``Nat`` and its constructors
   ``zero`` and ``suc`` from the Agda Builtin Library.
3. declaration of the datatype ``Vec``.
4. declaration of the empty vector constructor ``[]``.
5. declaration of the append constructor ``_∷_``
6. specification of the :ref:`precedence` for the append operation

.. note:: Paste or type the code above in a new file with extension ``.agda``.
  Load the file with ``C-c C-l``. This also saves the file. You should see
  ***All done*** if the agda source code was loaded correctly. Find more
  information about errors in our
  `issue tracker <https://github.com/agda/agda/issues>`_.

Infer the type of ``3 ∷ 2 ∷ 1 ∷ []``
------------------------------------

As an exercise, you can let Agda infer the type of some vectors with ``C-c C-d``.
Type a vector, for instance ``3 ∷ 2 ∷ 1 ∷ []``, press ``Return`` and Agda
will infer its type and return ``Vec Nat 3`` as expected.

.. note:: See :ref:`notation-for-key-combinations` for a full list of
  interactive commands (keybindings).

The datatype ``Vec``
--------------------

Our goal is to define a type of vectors with components of type ``A`` and
length ``n``. In Agda, we can freely choose all identifiers, we opted here
for the standard ``Vec``, but any other valid identifier will work, like
``Vector`` or ``V``.

``Vec A n`` is the family of types that represent the collection
of vector spaces. This family of types is indexed by the dimension, i.e. by
objects of ``Nat`` (the set of natural numbers). The components of the vector
can belong to an arbitrary element type that we represented with the identifier
``A`` (again, ``A`` could have been ``X`` or any other valid identifier; ``n``
could have been ``m`` and so on).

We refer to ``A`` as the *parameter* of the datatype ``Vec A n``. So far, we
know that the index ``n`` is a natural number, but we also need to know what
is ``A``. We will specify that A can be any element type of the sort ``Set``,
but it could have been any other sort with a greater level of abstraction. We
express the fact that ``A`` has type ``Set`` or ``A`` ranges over ``Set`` by
means of the colon ``:``.

We can infer that ``Vec A n`` will also range over ``Set`` (the lower upper
bound of the types involved). We are now entitled to write the signature of
our datatype: ``Vec (A : Set) : ℕ → Set``.

To declare the datytype, we place its signature between the keywords ``data``
and ``where``.

The constructors ``[]`` and ``_∷_``
-----------------------------------

Constructors are declared in new lines and indented with two spaces.

We chose for the first constructor the identifier ``[]``. It represents the
empty vector, and its type is the vector space of length ``0``.

The second constructor is a :ref:`mixfix operator <mixfix-operators>` named
``_∷_`` (pronounced append). For all numbers, it takes as input an element
of ``A`` and a vector. As output, it produces a vector with a length
increased by one.

The declaration with keyword ``ìnfixr`` does not belong to the datatype
declaration; therefore it is not indented. It establishes the
:ref:`precedence <precedence>` of the operator append. This finishes our
explanation of the ‘Hello world’ dependent type example.

‘Hello world’ proof
===================

We will see in this section how to enunciate and prove with Agda the
associativity of natural numbers under the addition. This time we will build
the code line by line. You can load the file in each step.

Enunciation of associativity
----------------------------

Please create a new ``.agda`` file named ``hello-world-proof.agda``.
Paste or type the following code:

.. code-block:: agda

  module hello-world-proof where

Loading the file with ``C-c C-l`` should work. This is fon now the empty
module. Now we bring to scope the datatype ``Nat`` and the addition operation
``_+_``, both defined in the Agda Builtin library.

.. code-block:: agda

  open import Agda.Builtin.Nat using (Nat ; _+_)

Next, we import the propositional equality between two terms ``_≡_``. This will
allow us to state that two terms compute to the same normal form.

.. code-block:: agda

  open import Agda.Builtin.Equality using (_≡_)

Now we can enunciate the associativity: given three (possibly different)
natural numbers, adding the first to the addition of the second and the third
computes to the same value as adding the addition of the first and the second
to the third. We will name this statement ``+assoc-enun``.

.. code-block:: agda

  +assoc-enun : Set
  +assoc-enun = ∀ (x y z : Nat) → x + (y + z) ≡ (x + y) + z

As an exercise, you can load the file with ``C-c C-l`` and then compute the
normal form of ``+assoc-enun`` with ``C-c C-d``.

.. note:: See :ref:`notation-for-key-combinations` for a full list of
  interactive commands (keybindings).

Proof of associativity
----------------------

Note that the statement ``+assoc-enun`` is a member of ``Set``. Now that we
were able to state the property in a way that Agda understands, our objective
is to prove it.

First, we will need to import the constructors ``zero`` and ``suc`` of the
already imported datatype ``Nat`` and the definition ``cong`` from the
`standard library <std-lib_>`_..

.. code-block:: agda

  open import Agda.Builtin.Nat using (zero ; suc)
  open import Relation.Binary.PropositionalEquality using (cong)
  open import Agda.Builtin.Equality using (refl)

In order to prove ``+assoc-enun`` we need just to find an element of that type.
We will name this element ``+assoc``, but like always one can go ahead and try
to find a better name, or a name that is more suitable for a certain context.

.. code-block:: agda

  +assoc : ∀ (x y z : Nat) → x + (y + z) ≡ (x + y) + z

If we load now the file, Agda will complain. The name ``+assoc`` was declared
correctly but a definition was not provided. That definition is actually the
proof that we are looking for. To build the definition, we need to know more
about holes and case splitting.

Holes and case splitting
------------------------

Agda will help us to find the proof by using its interactive mode. We will
first write a very simple clause so the file can be loaded even if we still
do not know the proof. The clause consists of the name of the property, the
input variables, the symbol equal ``=`` and the question mark ``?``.

.. code-block:: agda

  +assoc x y z = ?

Now Agda is not throwing an error when loading the file, but returning
***All Goals***. We have entered the interactive proving mode. Agda turns
our question mark into what is called a *hole* ``{!  0!}``. The number
``0`` inside labels the goal.

The next step would be choosing the pattern variable and perform case
splitting on it. Put the cursor inside the hole and press ``C-c C-c``.
Agda will ask for the pattern variable, let's write ``x`` and press
``Return``.

.. code-block:: agda

  +assoc zero y z = {!  0!}
  +assoc (suc x) y z = {!  1!}

Agda performs the case splitting of the clause, now we have one clause for
the case ``zero`` and another for the case ``suc x``. That means also that
we have two holes. The first one is easy to resolve, because when the case
of ``x`` is ``zero``, the equivalence that we want to prove holds
definitionally.

.. note:: The case splitting on the variable ``x`` is complete.
  Proving the definition for ``zero`` and ``suc x`` amounts to proving it
  for every ``x : Nat``.

Put the cursor inside the first hole labeled ``0`` and press ``C-c C-r``
to resolve it.

.. code-block:: agda

  +assoc x y z = refl
  +assoc (suc x) y z = {!  1!}

Now we have again one hole to resolve. If you load the file again, you will
get the type of the term that should be in the hole
``?0 : suc x + (y + z) ≡ suc x + y + z``. It seems like proving ``+assoc``
for the case ``suc x`` amounts to proving ``+assoc`` for ``x`` and then
applying the ``suc`` function to both sides of the equivalence. We can get the
latter with ``cong suc``.

Go ahead and infer its type with ``C-c C-d``. Agda returns
``{x y : Nat} → x ≡ y → suc x ≡ suc y``. ``cong suc`` takes as input a proof
of an equivalence and produces an equivalence of ``suc`` applied to both
sides, just what we were looking for.

Write ``cong suc`` after the ``=`` and before the hole now labeled ``0`` again
and load the file. Now the goal is just proving
``?0 : x + (y + z) ≡ x + y + z``, which is the proof of ``+assoc x y z``.

As it is structurally smaller than ``+assoc (suc x) y z``, we can recursively
use it as a proof. The result of the definition we were looking for is:

.. code-block:: agda

  +assoc x y z = refl
  +assoc (suc x) y z = cong suc (+assoc x y z)

Now just load the file again and you will see ***All Done***. This means that
indeed ``+assoc`` is a member of ``+assoc-enun`` and therefore its proof.

.. important::
  The ``x`` in the type signature of ``+assoc`` is **not** the same as the
  ``x`` pattern variable in the last clause where ``suc x`` is written. The
  following would work also: ``+assoc (suc x₁) y z = cong suc (+assoc x₁ y z)``.
  The scope of a variable declared in a signature is restricted to the
  signature itself.

Here is the final code of the ‘Hello world’ proof example:

.. code-block:: agda

  module hello-world-proof where

  open import Agda.Builtin.Nat using (Nat ; _+_)
  open import Agda.Builtin.Equality using (_≡_)

  +assoc-enun : Set
  +assoc-enun = ∀ (x y z : Nat) → x + (y + z) ≡ (x + y) + z

  open import Agda.Builtin.Nat using (zero ; suc)
  open import Relation.Binary.PropositionalEquality using (cong)
  open import Agda.Builtin.Equality using (refl)

  +assoc : ∀ (x y z : Nat) → x + (y + z) ≡ (x + y) + z
  +assoc zero y z = refl
  +assoc (suc x) y z = cong suc (+assoc x y z)

.. note:: You can learn more details about proving in the chapter
  `Proof by Induction <plfa-induction_>`_ of the
  `Programming Language Foundations in Agda <plfa_>`_ online book.

.. _plfa-induction: https://plfa.github.io/Induction/
.. _plfa: https://plfa.github.io

‘Hello world’ program
=====================

Agda is a dependently typed functional programming language. This entails the
fact that it is possible to write programs in Agda that interact with the
world. In this section, we will write a first ‘Hello world’ program in Agda
that we will be able to compile and execute right away.

Agda Source Code
----------------

First, we create a new file named ``hello-world-prog.agda`` with Emacs or Atom
in a folder that we will refer to as our top-level folder.

.. hint:: Agda programs are structured in :ref:`modules <module-system>`. The
  first module in each file is the *top-level* module whose name
  matches the filename.

.. code-block:: agda

  module hello-world-prog where

  open import Agda.Builtin.IO using (IO)
  open import Agda.Builtin.Unit using (⊤)
  open import Agda.Builtin.String using (String)

  postulate putStrLn : String → IO ⊤
  {-# FOREIGN GHC import qualified Data.Text as T #-}
  {-# COMPILE GHC putStrLn = putStrLn . T.unpack #-}

  main : IO ⊤
  main = putStrLn "Hello world!"

This code is self-contained and has several declarations:

1. imports of the ``ÌO``, ``⊤`` and ``String`` datatypes from the
   `standard library <std-lib_>`_.
2. postulate of the function type ``putStrLn``.
3. declaration of compilation :ref:`pragmas <pragmas>`.
4. definition of ``main``.

.. note:: Paste or type the code above in a new file with extension ``.agda``.
  Load the file with ``C-c C-l``. This also saves the file. You should see
  ***All done*** if the agda source code was loaded correctly. Find more
  information about errors in our
  `issue tracker <https://github.com/agda/agda/issues>`_.

Compilation with GHC Backend
----------------------------

Once loaded, you can compile the program directly from Emacs or Atom by
pressing ``C-c C-x C-c``. Alternatively, you can open a terminal session,
navigate to your top-level folder and run:

.. code-block::

  agda --compile hello-world-prog.agda

.. warning:: Frequent error when compiling: ``primFloatEquality`` requires the
  `ieee754 <http://hackage.haskell.org/package/ieee754>`_ haskell library.

The ``--compile`` flag here creates via the :ref:`GHC backend <ghc-backend>`
a binary file in the top-level folder that the computer can execute.

Finally, you can then run the executable (``./hello-world-prog`` on Unix
systems, ``hello-world-prog.exe`` on Windows) from the command line:

.. code-block::

  $ cd <your top-level folder>
  $ ./hello
  Hello, World!

.. tip:: A module exporting a function ``main : IO a`` can be :ref:`compiled
  <compiling-agda-programs>` to a standalone executable.  For example:
  ``main = run (putStrLn "Hello, World!")`` runs the ``IO`` command
  ``putStrLn "Hello, World!"`` and then quits the program.

.. _std-lib: https://github.com/agda/agda-stdlib

Compilation with JavaScript Backend
-----------------------------------

The :ref:`JavaScript backend <javascript-backend>` will translate the Agda
source code of the ``hello-world-prog.agda`` file to JavaScript code.

Open a terminal session, navigate to your top-level folder and run:

.. code-block::

  agda --js hello-world-prog.agda

This will create several ``.js`` files in your top-level folder. The file
corresponding to our source code will have the name
``jAgda.hello-world-prog.js``.

.. hint:: The additional ``--js-optimize`` flag typically makes the generated
  JavaScript code faster but less readable. On the other hand, the
  ``--js-minify`` flag makes the generated JavaScript code smaller and still
  less readable.
