.. _quick-guide:

*************************************************************
Quick Guide to Editing, Type Checking and Compiling Agda Code
*************************************************************

.. _quick-guide-introduction:

Introduction
============

Agda programs are commonly edited using `Emacs
<http://www.gnu.org/software/emacs/>`_ or `Atom
<https://atom.io/packages/agda-mode>`_. To edit a module (assuming you
have :ref:`installed <installation>` Agda and its Emacs mode (or
Atom's) properly), start the editor and open a file ending in
``.agda``. Programs are developed *interactively*, which means that
one can type check code which is not yet complete: if a question mark
(``?``) is used as a placeholder for an expression, and the buffer is
then checked, Agda will replace the question mark with a "hole" which
can be filled in later. One can also do various other things in the
context of a hole: listing the context, inferring the type of an
expression, and even evaluating an open term which mentions variables
bound in the surrounding context.

The following commands are the most common (see
:ref:`notation-for-key-combinations`):

:kbd:`C-c C-l`
     Load. Type-checks the contents of the file.

:kbd:`C-c C-,`
     Shows the goal type, i.e. the type expected in the
     current hole, along with the types of locally defined
     identifiers.

:kbd:`C-c C-.`
     A variant of ``C-c C-,`` that also tries to infer the
     type of the current hole's contents.

:kbd:`C-c C-SPC`
     Give. Checks whether the term written in the current
     hole has the right type and, if it does, replaces the hole with
     that term.

:kbd:`C-c C-r`
     Refine. Checks whether the return type of the
     expression ``e`` in the hole matches the expected type. If so,
     the hole is replaced by ``e { }1 ... { }n``, where a sufficient
     number of new holes have been inserted. If the hole is empty,
     then the refine command instead inserts a lambda or constructor
     (if there is a unique type-correct choice).

:kbd:`C-c C-c`
     Case split. If the cursor is positioned in a hole which
     denotes the right hand side of a definition, then this command
     automatically performs pattern matching on variables of your
     choice.

:kbd:`C-c C-n`
     Normalise. The system asks for a term which is then evaluated.

:kbd:`M-.`
     Go to definition. Goes to the definition site of the
     identifier under the cursor (if known).

:kbd:`M-*`
     Go back (Emacs < 25.1)

:kbd:`M-,`
     Go back (Emacs ≥ 25.1)

For information related to the Emacs mode (configuration, keybindings,
Unicode input, etc.) see :ref:`emacs-mode`.

Menus
=====
There are two main menus in the system:

* A main menu called **Agda2** which is used for global commands.

* A context sensitive menu which appears if you right-click in a hole.

The menus contain more commands than the ones listed above. See
:ref:`global <emacs-global-commands>` and :ref:`context sensitive
<emacs-context-sensitive-commands>` commands.

Writing mathematical symbols in source code
===========================================

Agda uses `Unicode <https://en.wikipedia.org/wiki/Unicode>`_
characters in source files (more specifically: the `UTF-8
<https://en.wikipedia.org/wiki/UTF-8>`_ character encoding). Almost
any character can be used in an identifier (like ``∀``, ``α``, ``∧``,
or ``♠``, for example). It is therefore necessary to have spaces
between most lexical units.

Many mathematical symbols can be typed using the corresponding `LaTeX
<https://en.wikipedia.org/wiki/LaTeX>`_ command names. For instance,
you type ``\forall`` to input ``∀``. A more detailed description of
how to write various characters is :ref:`available <unicode-input>`.


(Note that if you try to read Agda code using another program, then
you have to make sure that it uses the right character encoding when
decoding the source files.)

Errors
=======

If a file does not type check Agda will complain. Often the cursor
will jump to the position of the error, and the error will (by
default) be underlined. Some errors are treated a bit differently,
though. If Agda cannot see that a definition is terminating/productive
it will highlight it in *light salmon*, and if some meta-variable
other than the goals cannot be solved the code will be highlighted in
*yellow* (the highlighting may not appear until after you have
reloaded the file). In case of the latter kinds of errors you can
still work with the file, but Agda will (by default) refuse to import
it into another module, and if your functions are not terminating Agda
may hang.

If you do not like the way errors are highlighted (if you are
colour-blind, for instance), then you can tweak the settings by typing
``M-x customize-group RET agda2-highlight RET`` in Emacs (after
loading an Agda file) and following the instructions.

.. _compiling-agda-programs:

Compiling Agda programs
=======================

To compile a module containing a function ``main :: IO A`` for some
``A`` (where ``IO`` can be found in the `Primitive.agda
<https://github.com/agda/agda-stdlib/blob/master/src/IO/Primitive.agda>`_),
use ``C-c C-x C-c``. If the module is named ``A.B.C`` the resulting
binary will be called ``C`` (located in the project's top-level
directory, the one containing the ``A`` directory).

Batch-mode command
==================

There is also a batch-mode command line tool: ``agda``. To find out
more about this command, use ``agda --help``.
