
..
  ::
  module getting-started.a-taste-of-agda where

.. _a-taste-of-agda:

***************
A Taste of Agda
***************

This section's objective is providing the first glimpse of Agda with some
minimal examples. The first one is a demonstration of dependently typed
programming, and the second shows how to write proofs in Agda. Finally, we
build a complete program and compile it to an executable program with the GHC
and Javascript backends.

Before proceeding, make sure that you :ref:`installed Agda <installation>`
and a compatible version of the `standard library
<https://github.com/agda/agda-stdlib/blob/master/notes/installation-guide.md>`_.
You also need an editor with *interactive* capabilities, currently
supported editors are Emacs via the :ref:`Emacs mode <emacs-mode>`, Atom via
the `agda mode for Atom <atom_>`_ and VSCode via the
`agda mode for VSCode <vs-code_>`_.

.. _atom: https://atom.io/packages/agda-mode
.. _vs-code: https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode

.. note:: In this introduction we use several of Agda's interactive commands
  to get information from the typechecker and manipulate the code.
  See :ref:`notation-for-key-combinations` for a full list of
  interactive commands (keybindings).

.. hint:: If you want a sneak peek of Agda without installing it, try the
  `Agda Pad <agda-pad_>`_

.. _agda-pad: https://agdapad.quasicoherent.io/

Programming With Dependent Types: Vectors
=========================================

In the code below, we model the notion of *vectors* (in the sense of computer
science, not in the mathematical sense) in Agda. Roughly speaking, a vector is
a list of objects with a determined length.

.. code-block:: agda

  module hello-world-dep where

  open import Data.Nat using (ℕ ; zero ; suc)

  data Vec (A : Set) : ℕ → Set where
    []  : Vec A zero
    _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

  infixr 5 _∷_

.. note:: Paste or type the code above in a new file with extension ``.agda``.
  Load the file (in Emacs ``C-c C-l``). This also saves the file. You should
  see ***All done*** if the Agda source code was loaded correctly.

Agda programs are structured into :ref:`modules <module-system>`. Each Agda
file has one *top-level module* whose name must match the name of the file, and
zero or more nested modules. Each module that each contain a list of
*declarations*. This example has a single top-level module called
``hello-world-dep``, which has three declarations:

1. An *import* statement importing the datatype ``ℕ`` and its
   constructors ``zero`` and ``suc`` from the module
   ``Data.Nat`` of the standard library,
2. A *datatype definition* of the datatype ``Vec``, which has
   two constructors: the empty vector constructor ``[]`` and
   the *cons* constructor ``_∷_``,
3. And finally an ``infixr`` declaration specifying the
   :ref:`precedence <precedence>` for the *cons* operation.

.. note:: Agda code often makes use of unicode symbols, such as ``ℕ``, ``→``,
  and ``∷`` in this example. To learn how to enter a unicode character, move the
  cursor over it and enter ``M-x describe-char`` or ``C-u C-x =``. This displays
  all information on the character, including how to input it with the Agda
  input method. For example, to input ``ℕ`` you can type either ``\Bbb{N}``
  or ``\bN``.

The datatype ``Vec``
--------------------

Let us start by looking at the first line of the definition of
``Vec``::

  data Vec (A : Set) : ℕ → Set where

This line declares a new datatype and names it ``Vec``. The words ``data`` and
``where`` are keywords, while the part ``Vec (A : Set) : ℕ → Set`` determines
the type of ``Vec``.

``Vec`` is not a single type but rather a *family of types*. This family of
types has one *parameter* ``A`` of type ``Set`` (which is the type of all small
types such as ``ℕ``, ``Bool``, ...) and one *index* of type ``ℕ`` (the type of
natural numbers). The parameter ``A`` represents the type of the elements of
the vector. Meanwhile, the index represents the length of the vector, i.e. the
number of objects it contains.

Together, this line tells us that, for any concrete type ``B : Set``
and any natural number ``m : ℕ``, this definition gives us a new
type ``Vec B m``, which also belongs to ``Set``.


The constructors ``[]`` and ``_∷_``
-----------------------------------

Constructors are declared in new lines and indented with a strictly
positive number of spaces (in this case two).

We chose for the first constructor the identifier ``[]``. It
represents the empty vector, and its type is ``Vec A 0``, i.e. it is a
vector of length ``0``.

The second constructor is a :ref:`mixfix operator <mixfix-operators>`
named ``_∷_`` (pronounced *cons*). For any number ``n : ℕ``, it
takes as input an element of ``A`` and a vector of length ``n``. As
output, it produces a vector with length ``suc n``, the successor of
``n``.

The declaration with keyword ``ìnfixr`` does not belong to the
datatype declaration itself; therefore it is not indented. It
establishes the :ref:`precedence <precedence>` of the operator ``_∷_``.

.. note:: You can let Agda infer the type of an expression using the 'Deduce
  type' command (``C-c C-d``). First press ``C-c C-d`` to open a prompt, enter a
  term, for instance ``3 ∷ 2 ∷ 1 ∷ []``, and press return. Agda infers its
  type and return the ``Vec ℕ 3`` as expected.

The total function ``lookup``
-----------------------------

Now that ``Vec`` is defined, we continue by defining the ``lookup`` function
that given a vector and a position, returns the object of the
vector at the given position. In contrast to the ``lookup`` function
we could define in most (non-dependently typed) programming languages,
this version of the function is *total*: all calls to it are
guaranteed to return a value in finite time, with no possibility for
errors.

To do so, we use the ``Fin`` datatype from the standard
library. ``Fin n`` is a type with ``n`` elements, which we use to
model the ``n`` possible positions in a vector of length ``n``.

Now create a new file called ``hello-world-dep-lookup.agda`` file and type or paste:

.. code-block:: agda

  module hello-world-dep-lookup where

  open import Data.Nat using (ℕ)
  open import Data.Vec using (Vec ; _∷_)
  open import Data.Fin using (Fin ; zero ; suc)

  variable
    A : Set
    n : ℕ

  lookup : Vec A n → Fin n → A
  lookup (a ∷ as) zero = a
  lookup (a ∷ as) (suc i) = lookup as i


The ``Vec`` type that we saw before is actually already in the module
``Data.Vec`` of the standard library, so we import it instead of
copying the previous definition.

We have declared ``A`` and ``n`` as :ref:`generalizable variables
<generalization-of-declared-variables>` to avoid the declaration of
implicit arguments. This allows us to use ``A`` and ``n`` in the type
of ``lookup`` without binding the names explicitly. More explicitly,
the full type of ``lookup`` (which we can get by using ``C-c C-d``) is::

  lookup : {A : Set} → {n : ℕ} → Vec A n → Fin n → A

.. warning:: ``zero`` and ``suc`` are **not** the constructors of ``ℕ`` that we
  saw before, but rather the constructors of ``Fin``. Agda allows overloading of
  constructor names, and disambiguates between them based on the expected type
  where they are used.

The definition of the ``lookup`` function specifies two cases:

- Either the vector is ``a ∷ as`` and the position is ``zero``, so we
  return the first element ``a`` of the vector.

- Or the vector is ``a ∷ as`` and the position is ``suc i``, so we
  recursively look up the element at position ``i`` in the tail ``as``
  of the vector.

There are no cases for the empty vector ``[]``. This is no
mistake: Agda can determine from the type of ``lookup`` that it is
impossible to look up an element in the empty vector, since there is
no possible index of type ``Fin 0``. For more details, see the section
on :ref:`coverage checking <coverage-checking>`.

Agda as a Proof Assistant: Proving Associativity of Addition
============================================================

In this section we state and prove the associativity of addition on the natural
numbers in Agda. In contrast to the previous section, we build the code line by
line. If you are following this example in Emacs, you should reload your file
after adding each step by pressing ``C-c C-l``.

Statement of associativity
--------------------------

We start by creating a new file named ``hello-world-proof.agda``.
Paste or type the following code:

.. code-block:: agda

  module hello-world-proof where

Now we import the datatype ``ℕ`` and the addition operation
``_+_``, both defined in the Agda Builtin library.

.. code-block:: agda

  open import Data.Nat using (ℕ ; _+_)

Next, we import the *propositional equality type* ``_≡_`` from the module
``Relation.Binary.PropositionalEquality``.

.. code-block:: agda

  open import Relation.Binary.PropositionalEquality using (_≡_)

Under the `Curry-Howard correspondence
<https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence>`_, the type
``x ≡ y`` corresponds to the proposition stating that ``x`` and ``y`` are equal
objects. By writing a function that returns an element of type ``x ≡ y``, we
are *proving* that the two terms are equal.

Now we can state associativity: given three (possibly different) natural
numbers, adding the first to the addition of the second and the third
computes to the same value as adding the addition of the first and the second
to the third. We name this statement ``+-assoc-enun``.

.. code-block:: agda

  +-assoc-enun : Set
  +-assoc-enun = ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z

This is not yet a proof, we have merely written down the statement (or
*enunciation*) of associativity.

Proof of associativity
----------------------

The statement ``+-assoc-enun`` is a member of ``Set``, i.e. it is a
type. Now that we were able to state the property in a way that Agda
understands, our objective is to prove it. To do so, we have to
construct a function of type ``+-assoc-enun``.

First, we need to import the constructors ``zero`` and ``suc`` of the
already imported datatype ``ℕ`` and the constructor ``refl`` (short for
`reflexivity`) and function ``cong`` (short for `congruence`) from the
`standard library <std-lib_>`_.

.. code-block:: agda

  open import Data.Nat using (zero ; suc)
  open import Relation.Binary.PropositionalEquality using (refl; cong)

To prove ``+-assoc-enun`` we need to find an element of that
type. Here, we name this element ``+-assoc``.

.. code-block:: agda

  +-assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z

If we load now the file, Agda gives an error: ``The following names are
declared but not accompanied by a definition: +-assoc``. Indeed, we have only
declared the type of ``+-assoc`` but not yet given a definition. To build the
definition, we need to know more about holes and case splitting.

Holes and case splitting
------------------------

Agda can help us to find the proof by using its interactive mode. To start, we
first write a simple clause so the file can be loaded even if we still do
not know the proof. The clause consists of the name of the property, the input
variables, the symbol equal ``=`` and the question mark ``?``.

.. code-block:: agda

  +-assoc x y z = ?

When we reload the file, Agda no longer throws an error, but instead shows the
message ***All Goals*** with a list of goals. We have entered the interactive
proving mode. Agda turns our question mark into what is called a *hole* ``{ }0``.
The number ``0`` inside labels the goal.

To continue writing our proof, we now pick a variable and perform a case
split on it. To do so, put the cursor inside the hole and press ``C-c C-c``.
Agda prompts you for the name of the pattern variable to case on. Let's
write ``x`` and press ``Return``. This replaces the previous clause with
two new clauses, one where ``x`` has been replaced by ``zero`` and another
where it has been replaced by ``suc x``:

.. code-block:: agda

  +-assoc zero y z = {  }0
  +-assoc (suc x) y z = {  }1

Instead of one hole, we now have two. To get detailed information about a
specific hole, put your cursor in it and press ``C-c C-,``. This displays
the type of the hole, as well as the types of all the variables in scope.

The first hole has type ``y + z ≡ y + z``, which is easy to resolve. To do so,
put the cursor inside the first hole labeled ``0`` and press ``C-c C-r``. This
replaces the hole by the term ``refl``, which stands for `reflexivity` and
can be used any time we want to construct a term of type ``w ≡ w`` for some
term ``w``.

.. code-block:: agda

  +-assoc x y z = refl
  +-assoc (suc x) y z = {  }1

Now we have one hole left to resolve. By putting the cursor in it and pressing
``C-c C-,`` again, we get the type of the hole: ``suc x + (y + z) ≡ suc x + y +
z``. Agda has already applied the definition of ``_+_`` to replace
the left-hand side ``(suc x + y) + z`` of the equation by ``suc (x + y + z)``,
and similarly replaced the right-hand side ``suc x + (y + z)`` by ``suc (x + (y
+ z))``.

.. tip:: You can use the ``go-to-definition`` command by selecting the
  definition that you want to check eg. ``_+_`` and pressing ``M-.`` in Emacs or
  ``C-M-\`` in Atom. This takes you to the definition of ``_+_``, which is
  originally defined in the builtin module ``Agda.Builtin.Nat``.

.. tip:: You can ask Agda to compute the normal form of a term. To do so,
  place the cursor in the remaining hole (which should not contain any text at
  this point) and press ``C-c C-n``. This prompts you for an expression to
  normalize. For example, if we enter ``(suc x + y) + z`` we get back
  ``suc (x + y + z)`` as a result.

.. note::
  You might wonder why Agda displays the term ``(x + y) + z`` as ``x +
  y + z`` (without parenthesis). This is done because of the infix statement
  ``infixl 6 _+_`` that was declared in the imported ``Agda.Builtin.Nat`` module.
  This declaration means that the ``_+_`` operation is left-associative. More
  information about :ref:`mixfix operator <mixfix-operators>` like the arithmetic
  operations. You can also check :ref:`this associativity example
  <associativity>`.

Recursive call on ``+-assoc``
-----------------------------

If we now look at the type of the remaining hole, we see that both the
left-hand side and the right-hand side start with an application of the
constructor ``suc``. In this kind of situation it suffices to prove that the
two arguments to ``suc`` are equal. This principle is called congruence of
equality, and it is expressed by the Agda function ``cong``.

To use ``cong`` we need to apply it to a function or constructor, in this case
``suc``. We can ask Agda to infer the type of ``cong suc`` by pressing ``C-c
C-d`` and entering the term. We get back the type ``{x y : ℕ} → x ≡ y →
suc x ≡ suc y``. In other words, ``cong suc`` takes as input a proof of an
equivalence and produces an equivalence of ``suc`` applied to both sides, which
is exactly what we need. We write ``cong suc`` in the hole and again press
``C-c C-r`` to refine the hole. This results in the new line

.. code-block:: agda

  +-assoc (suc x) y z = cong suc {  }2

together with a new hole of type ``x + (y + z) ≡ x + y + z``.

To finish the proof, we now make a recursive call ``+-assoc x y z``. Note
that this has exactly the type we need. To complete the proof, we hence
type it into the hole and solve it with ``C-c C-space``.

When we define a recursive function like this, Agda performs :ref:`termination
checking <termination-checking>` on it. This is important to ensure the
recursion is well-founded, and hence will not result in an invalid (circular)
proof. In this case, the first argument ``x`` is structurally smaller than the
first argument ``suc x`` on the left-hand side of the clause, hence Agda
allows us to make the recursive call. Because termination is an
undecidable property, Agda will not accept all terminating functions, but only
the ones that are mechanically proved to terminate.

The result of the definition we were looking for is:

.. code-block:: agda

  +-assoc x y z = refl
  +-assoc (suc x) y z = cong suc (+-assoc x y z)

When we reload the file, we see ***All Done***. This means that
``+-assoc`` is indeed a proof of the statement ``+-assoc-enun``.

.. important::
  The ``x`` in the type signature of ``+-assoc`` is **not** the same as the
  ``x`` pattern variable in the last clause where ``suc x`` is written. The
  following would also work: ``+-assoc (suc x₁) y z = cong suc (+-assoc x₁ y z)``.
  The scope of a variable declared in a signature is restricted to the
  signature itself.

Here is the final code of the ‘Hello world’ proof example:

.. code-block:: agda

  module hello-world-proof where

  open import Agda.Builtin.Nat using (ℕ ; _+_)
  open import Agda.Builtin.Equality using (_≡_)

  +-assoc-enun : Set
  +-assoc-enun = ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z

  open import Agda.Builtin.Nat using (zero ; suc)
  open import Relation.Binary.PropositionalEquality using (cong)
  open import Agda.Builtin.Equality using (refl)

  +-assoc : ∀ (x y z : Nat) → x + (y + z) ≡ (x + y) + z
  +-assoc zero y z = refl
  +-assoc (suc x) y z = cong suc (+-assoc x y z)

.. note::
  You can learn more details about proving in the chapter
  `Proof by Induction <plfa-induction_>`_ of the online book
  `Programming Language Foundations in Agda <plfa_>`_.

.. _plfa-induction: https://plfa.github.io/Induction/
.. _plfa: https://plfa.github.io

Building an Executable Agda Program
===================================

Agda is a dependently typed functional programming language. This means that we
can write programs in Agda that interact with the world. In this section, we
write a small ‘Hello world’ program in Agda, compile it, and execute it.
In contrast to the standalone example on the :ref:`Hello World page
<hello-world>`, here we make use of the standard library to write a
shorter version of the same program.

Agda Source Code
----------------

First, we create a new file named ``hello-world-prog.agda`` with Emacs or Atom
in a folder that we refer to as our top-level folder.

.. code-block:: agda

  module hello-world-prog where

  open import Level
  open import IO

  main = run {0ℓ} (putStrLn "Hello, World!")

A quick line-by-line explanation:

* The first line declares the top-level module, named ``hello-world-prog``.

* The second and third lines import the ``Level`` and ``IO`` modules from the
  `standard library <std-lib_>`_ and bring their contents into scope.

* A module exporting a function ``main`` of the right type can be
  :ref:`compiled <compiling-agda-programs>` to a standalone executable. For
  example: ``main = run {0ℓ} (putStrLn "Hello, World!")`` runs the ``IO`` command
  ``putStrLn "Hello, World!"`` and then quits the program.

.. note:: Paste or type the code above in a new file with name
  ``hello-world-prog.agda``. Load the file (in Emacs ``C-c C-l``). This also
  saves the file. If the agda source code was loaded correctly, you should see
  that the code is highlighted and see a message ***All done*** .

Compilation with GHC Backend
----------------------------

Once loaded, you can compile the program directly from Emacs or Atom by
pressing ``C-c C-x C-c`` and entering ``GHC``. Alternatively, you can open a
terminal session, navigate to your top-level folder and run:

.. code-block::

  agda --compile hello-world-prog.agda

The ``--compile`` flag here creates via the :ref:`GHC backend <ghc-backend>`
a binary file in the top-level folder that the computer can execute.

Finally, you can then run the executable (``./hello-world-prog`` on Unix
systems, ``hello-world-prog.exe`` on Windows) from the command line:

.. code-block::

  $ cd <your top-level folder>
  $ ./hello-world-prog
  Hello, World!

.. tip:: Any top-level module exporting a function ``main : IO a`` can be :ref:`compiled
  <compiling-agda-programs>` to a standalone executable.

.. _std-lib: https://github.com/agda/agda-stdlib

Compilation with JavaScript Backend
-----------------------------------

The :ref:`JavaScript backend <javascript-backend>` translates the Agda
source code of the ``hello-world-prog.agda`` file to JavaScript code.

From Emacs or Atom, press ``C-c C-x C-c`` and enter ``JS`` to compile the
module to JavaScript. Alternatively, open a terminal session, navigate to your
top-level folder and run:

.. code-block::

  agda --js hello-world-prog.agda

This creates several ``.js`` files in your top-level folder. The file
corresponding to our source code has the name
``jAgda.hello-world-prog.js``.

.. hint:: The additional ``--js-optimize`` flag can be used to make the generated
  JavaScript code faster but less readable. Moreover, the
  ``--js-minify`` flag makes the generated JavaScript code smaller and even
  less readable.

Where to go from here?
======================

There are many books and tutorials on Agda. We recommend this
:ref:`list of tutorials <tutorial-list>`.

Join the Agda Community!
------------------------

Get in touch and join the `Agda community <agda-community_>`_, or join the conversation on the
`Agda Zulip <agda-zulip_>`_.

.. _agda-community: https://github.com/agda
.. _agda-zulip: https://agda.zulipchat.com
