..
  ::
  module language.lexical-structure where

  open import Agda.Builtin.String

.. _lexical-structure:

*****************
Lexical Structure
*****************

Agda code is written in UTF-8 encoded plain text files with the
extension ``.agda``. Most unicode characters can be used in
identifiers and whitespace is important, see :ref:`names` and
:ref:`lexical-structure-layout` below.

Tokens
------

.. _keywords-and-special-symbols:

Keywords and special symbols
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Most non-whitespace unicode can be used as part of an Agda name, but there are
two kinds of exceptions:

special symbols
  Characters with special meaning that cannot appear at all in a name. These are
  ``.;{}()@"``.

keywords
  Reserved words that cannot appear as a :ref:`name part <names>`, but
  can appear in a name together with other characters.

  ``=`` ``|`` ``->`` ``→`` ``:`` ``?`` ``\`` ``λ``
  :ref:`∀ <notational-conventions>` ``..`` ``...``
  ``abstract``
  ``coinductive``
  ``constructor``
  ``data``
  :ref:`do <do-notation>`
  ``eta-equality``
  ``field``
  :ref:`forall <notational-conventions>`
  ``hiding``
  ``import``
  ``in``
  ``inductive``
  ``infix``
  ``infixl``
  ``infixr``
  ``instance``
  ``interleaved``
  ``let``
  :ref:`macro <macros>`
  ``module``
  ``mutual``
  ``no-eta-equality``
  ``open``
  :ref:`overlap <instance-fields>`
  ``pattern``
  ``postulate``
  ``primitive``
  ``private``
  ``public``
  :ref:`quote <reflection>`
  :ref:`quoteTerm <macros>`
  ``record``
  ``renaming``
  ``rewrite``
  ``Set``
  ``syntax``
  ``tactic``
  :ref:`unquote <macros>`
  :ref:`unquoteDecl <unquoting-declarations>`
  :ref:`unquoteDef <unquoting-declarations>`
  ``using``
  :ref:`variable <generalization-of-declared-variables>`
  ``where``
  ``with``

  The ``Set`` keyword can appear with a natural number suffix, optionally
  subscripted (see :ref:`sort-system`). For instance ``Set42`` and
  ``Set₄₂`` are both keywords.

keywords in ``renaming`` directives
  The following words are only reserved in ``renaming`` directives:

  ``to``

.. _names:

Names
~~~~~

A `qualified name` is a non-empty sequence of `names` separated by
dots (``.``). A `name` is an alternating sequence of `name parts` and
underscores (``_``), containing at least one name part. A `name part`
is a non-empty sequence of unicode characters, excluding whitespace,
``_``, and :ref:`special symbols <keywords-and-special-symbols>`. A
name part cannot be one of the
:ref:`keywords <keywords-and-special-symbols>` above, and cannot start
with a single quote, ``'`` (which are used for character literals, see
Literals_ below).

Examples
  - Valid: ``data?``, ``::``, ``if_then_else_``, ``0b``, ``_⊢_∈_``, ``x=y``
  - Invalid: ``data_?``, ``foo__bar``, ``_``, ``a;b``, ``[_.._]``

The underscores in a name indicate where the arguments go when the name is used
as an operator. For instance, the application ``_+_ 1 2`` can be written as ``1
+ 2``. See :ref:`mixfix-operators` for more information. Since most sequences
of characters are valid names, whitespace is more important than in other
languages. In the example above the whitespace around ``+`` is required, since
``1+2`` is a valid name.


Qualified names are used to refer to entities defined in other modules. For
instance ``Prelude.Bool.true`` refers to the name ``true`` defined in the
module ``Prelude.Bool``. See :ref:`module-system` for more information.

.. _lexical-structure-literals:

Literals
~~~~~~~~

There are four types of literal values: integers, floats, characters, and
strings. See :ref:`built-ins` for the corresponding types, and
:ref:`literal-overloading` for how to support literals for user-defined types.

.. _lexical-structure-int-literals:

Integers
  Integer values in decimal, hexadecimal (prefixed by ``0x``), or binary
  (prefixed by ``0b``) notation. The character `_` can be used to separate
  groups of digits. Non-negative numbers map by default to :ref:`built-in
  natural numbers <built-in-nat>`, but can be overloaded. Negative numbers have
  no default interpretation and can only be used through :ref:`overloading
  <literal-overloading>`.

  Examples: ``123``, ``0xF0F080``, ``-42``, ``-0xF``, ``0b11001001``,
  ``1_000_000_000``, ``0b01001000_01001001``.

.. _lexical-structure-float-literals:

Floats
  Floating point numbers in the standard notation (with square brackets
  denoting optional parts):

  .. code-block:: none

     float    ::= [-] decimal . decimal [exponent]
                | [-] decimal exponent
     exponent ::= (e | E) [+ | -] decimal

  These map to :ref:`built-in floats <built-in-float>` and cannot be overloaded.

  Examples: ``1.0``, ``-5.0e+12``, ``1.01e-16``, ``4.2E9``, ``50e3``.

.. _characters:
.. _lexical-structure-char-literals:

Characters
  Character literals are enclosed in single quotes (``'``). They can be a
  single (unicode) character, other than ``'`` or ``\``, or an escaped
  character. Escaped characters start with a backslash ``\`` followed by an
  escape code. Escape codes are natural numbers in decimal or hexadecimal
  (prefixed by ``x``) between ``0`` and ``0x10ffff`` (``1114111``), or one of
  the following special escape codes:

  ======== ======== ======== ======== ======== ======== ======== ========
  Code     ASCII    Code     ASCII    Code     ASCII    Code     ASCII
  ======== ======== ======== ======== ======== ======== ======== ========
  ``a``    7        ``b``    8        ``t``    9        ``n``    10
  ``v``    11       ``f``    12       ``\``    ``\``    ``'``    ``'``
  ``"``    ``"``    ``NUL``  0        ``SOH``  1        ``STX``  2
  ``ETX``  3        ``EOT``  4        ``ENQ``  5        ``ACK``  6
  ``BEL``  7        ``BS``   8        ``HT``   9        ``LF``   10
  ``VT``   11       ``FF``   12       ``CR``   13       ``SO``   14
  ``SI``   15       ``DLE``  16       ``DC1``  17       ``DC2``  18
  ``DC3``  19       ``DC4``  20       ``NAK``  21       ``SYN``  22
  ``ETB``  23       ``CAN``  24       ``EM``   25       ``SUB``  26
  ``ESC``  27       ``FS``   28       ``GS``   29       ``RS``   30
  ``US``   31       ``SP``   32       ``DEL``  127
  ======== ======== ======== ======== ======== ======== ======== ========

  Character literals map to the :ref:`built-in character type <built-in-char>` and
  cannot be overloaded.

  Examples: ``'A'``, ``'∀'``, ``'\x2200'``, ``'\ESC'``, ``'\32'``, ``'\n'``,
  ``'\''``, ``'"'``.

.. _lexical-structure-string-literals:

Strings
  String literals are sequences of, possibly escaped, characters
  enclosed in double quotes ``"``. They follow the same rules as
  :ref:`character literals <characters>` except that double quotes
  ``"`` need to be escaped rather than single quotes ``'``. String
  literals map to the :ref:`built-in string type <built-in-string>` by
  default, but can be :ref:`overloaded <overloaded-strings>`.

  Example: ``"Привет \"мир\"\n"``.

Holes
~~~~~

Holes are an integral part of the interactive development supported by the
:any:`Emacs mode <emacs-mode>`. Any text enclosed in ``{!`` and ``!}`` is a
hole and may contain nested holes. A hole with no contents can be written
``?``. There are a number of Emacs commands that operate on the contents of a
hole. The type checker ignores the contents of a hole and treats it as an
unknown (see :ref:`implicit-arguments`).

Example: ``{! f {!x!} 5 !}``

Comments
~~~~~~~~

Single-line comments are written with a double dash ``--`` followed by
arbitrary text. Multi-line comments are enclosed in ``{-`` and ``-}``
and can be nested.  Comments cannot appear in :ref:`string
literals <lexical-structure-string-literals>`.

Example::

  {- Here is a {- nested -}
     comment -}
  s : String --line comment {-
  s = "{- not a comment -}"

Pragmas
~~~~~~~

Pragmas are special comments enclosed in ``{-#`` and ``#-}`` that have special
meaning to the system. See :ref:`pragmas` for a full list of pragmas.

.. _lexical-structure-layout:

Layout
------

Agda is layout sensitive using similar rules as Haskell, with the exception
that layout is mandatory: you cannot use explicit ``{``, ``}`` and ``;`` to
avoid it.

A layout block contains a sequence of `statements` and is started by one of the
layout keywords:

.. code-block:: none

   abstract
   constructor
   do
   field
   instance
   let
   macro
   mutual
   postulate
   primitive
   private
   variable
   where

The first token after the layout keyword decides the indentation of the block.
Any token indented more than this is part of the previous statement, a token at
the same level starts a new statement, and a token indented less lies outside
the block.

::

  data Nat : Set where -- starts a layout block
      -- comments are not tokens
    zero : Nat      -- statement 1
    suc  : Nat →    -- statement 2
           Nat      -- also statement 2

  one : Nat -- outside the layout block
  one = suc zero

Note that the indentation of the layout keyword does not matter.

If several layout blocks are started by layout keywords without line
break in between (where line breaks inside block comments do not
count), then those blocks indented *more* than the last block go
passive, meaning they cannot be further extended by new statements::

  private module M where postulate
            A : Set                 -- module-block goes passive
            B : Set                 -- postulate-block can still be extended
          module N where            -- private-block can still be extended

An Agda file contains one top-level layout block, with the special rule that
the contents of the top-level module need not be indented.

::

  module Example where
  NotIndented : Set₁
  NotIndented = Set

Literate Agda
-------------

Agda supports `literate programming <literate_>`_ with multiple typesetting
tools like LaTeX, Markdown and reStructuredText. For instance, with LaTeX,
everything in a file is a comment unless enclosed in ``\begin{code}``,
``\end{code}``. Literate Agda files have special file extensions, like
``.lagda`` and ``.lagda.tex`` for LaTeX, ``.lagda.md`` for Markdown,
``.lagda.rst`` for reStructuredText instead of ``.agda``. The main use case
for literate Agda is to generate LaTeX documents from Agda code. See
:any:`generating-html` and :any:`generating-latex` for more information.

.. code-block:: latex

  \documentclass{article}
  % some preamble stuff
  \begin{document}
  Introduction usually goes here
  \begin{code}
  module MyPaper where
    open import Prelude
    five : Nat
    five = 2 + 3
  \end{code}
  Now, conclusions!
  \end{document}

.. _literate: https://en.wikipedia.org/wiki/Literate_programming
