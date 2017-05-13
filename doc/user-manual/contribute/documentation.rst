.. _documentation:

*************
Documentation
*************

Documentation is written in `reStructuredText format`_.

The Agda documentation is shipped together with the main Agda
repository in the ``doc/user-manual`` subdirectory. The content of
this directory is automatically published to https://agda.readthedocs.io.

Rendering documentation locally
===============================

* To build the user manual locally, you need to install
  the following dependencies:

    - Python ≥3.3

    - ``Sphinx`` and ``sphinx-rtd-theme``

        pip install --user -r doc/user-manual/requirements.txt

      Note that the ``--user`` option puts the Sphinx binaries in
      ``$HOME/.local/bin``.

    - LaTeX

  To see the list of available targets, execute ``make help``
  in ``doc/user-manual``. E.g., call ``make html`` to build the
  documentation in html format.

Type-checking code examples
===========================

You can include code examples in your documentation.

If your give the documentation file the extension ``.lagda.rst``, Agda will
recognise it as an Agda file and type-check it.

.. tip::

   If you edit ``.lagda.rst`` documentation files in Emacs, you can use Agda's interactive
   mode to write your code examples. Run ``M-x agda2-mode`` to switch to Agda
   mode, and ``M-x rst-mode`` to switch back to rST mode.



You can check that all the examples in the manual are type-correct by
running ``make user-manual-test`` from the root directory. This check
will be run as part of the continuous integration build.

.. warning::

   Remember to run ``fix-agda-whitespace`` to remove trailing whitespace
   before submitting the documentation to the repository.


Syntax for code examples
========================

The syntax for embedding code examples depends on:

  #. Whether the code example should be *visible* to the reader of the documentation.
  #. Whether the code example contains *valid* Agda code (which should be type-checked).


Visible, checked code examples
------------------------------

This is code that the user will see, and that will be also checked for
correctness by Agda.  Ideally, all code in the documentation should be
of this form: both *visible* and *valid*.


.. code-block:: rst

   It can appear stand-alone:

   ::

      data Bool : Set where
        true false : Bool


   Or at the end of a paragraph::

      data Bool : Set where
        true false : Bool

   Here ends the code fragment.

**Result:**

   It can appear stand-alone:

   ::

      data Bool : Set where
        true false : Bool


   Or at the end of a paragraph::

      data Bool : Set where
        true false : Bool

   Here ends the code fragment.



.. warning:: Remember to always leave a blank like after the ``::``.
         Otherwise, the code will be checked by Agda, but it will appear
         as regular paragraph text in the documentation.

Visible, unchecked code examples
--------------------------------

This is code that the reader will see, but will not be checked by Agda. It is
useful for examples of incorrect code, program output, or code in languages
different from Agda.

.. code-block:: rst

   .. code-block:: agda

      -- This is not a valid definition

      ω : ∀ a → a
      ω x = x


   .. code-block:: haskell

      -- This is haskell code

      data Bool = True | False

**Result:**

   .. code-block:: agda

      -- This is not a valid definition

      ω : ∀ a → a
      ω x = x


   .. code-block:: haskell

      -- This is haskell code

      data Bool = True | False



Invisible, checked code examples
--------------------------------

This is code that is not shown to the reader, but which is used to typecheck
the code that is actually displayed.

This might be definitions that are well known enough that do not need to be
shown again.

.. code-block:: rst

   ..
     ::
     data Nat : Set where
       zero : Nat
       suc  : Nat → Nat

   ::

     add : Nat → Nat → Nat
     add zero y = y
     add (suc x) y = suc (add x y)

**Result:**

   ..
     ::
     data Nat : Set where
       zero : Nat
       suc  : Nat → Nat

   ::

     add : Nat → Nat → Nat
     add zero y = y
     add (suc x) y = suc (add x y)




--------------
File structure
--------------

Documentation literate files (`.lagda.*`) are type-checked as whole Agda files,
as if all literate text was replaced by whitespace. Thus, **indentation** is
interpreted globally.


Namespacing
-----------

In the documentation, files are typechecked starting from the `doc/user-manual/`
root. For example, the file `doc/user-manual/language/data-types.lagda.rst`
should start with a hidden code block declaring the name of the module as
`language.data-types`:

.. code-block:: rst

   ..
     ::
     module language.data-types where

Scoping
-------

Sometimes you will want to use the same name in different places in the same
documentation file. You can do this by using hidden module declarations to
isolate the definitions from the rest of the file.

.. code-block:: rst

   ..
     ::
     module scoped-1 where

   ::

       foo : Nat
       foo = 42

   ..
     ::
     module scoped-2 where

     ::
       foo : Nat
       foo = 66


**Result:**

   ..
     ::
     module scoped-1 where

   ::

       foo : Nat
       foo = 42

   ..
     ::
     module scoped-2 where

     ::
       foo : Nat
       foo = 66




















.. _`reStructuredText format`: http://docutils.sourceforge.net/docs/ref/rst/restructuredtext.html

