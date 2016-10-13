.. _documentation:

*************
Documentation
*************

.. note::
   This is a stub.

Documentation is written in `reStructuredText format`_.

Code examples
=============

You can include code examples in your documentation.

If your give the documentation file the extension ``.lagda.rst``, code
examples in the  can be checked as part of the continuous integration. This
way, they will be guaranteed to always work with the latest version of
Agda.

.. tip::

   If you edit documentation files in Emacs, you can use Agda's interactive
   mode to write your code examples. Use ``M-x agda2-mode`` to switch to Agda
   mode, and ``M-x rst-mode`` to switch back to rST mode.


------
Syntax
------

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



.. tip:: Remember to always leave a blank like after the ``::``.
         Otherwise, the code will be checked by Agda, but it will appear
         variable-width paragraph text in the documentation.

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

