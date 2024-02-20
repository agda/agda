.. _emacs-mode:

**********
Emacs Mode
**********

Agda programs are commonly edited using `Emacs
<http://www.gnu.org/software/emacs/>`_ which is explained in this
section.  Other editors with interactive support for Agda include Atom
(`agda-mode on Atom <https://atom.io/packages/agda-mode>`_), Visual
Studio Code (`agda-mode on VS Code
<https://github.com/banacorn/agda-mode-vscode>`_), and Vim (`agda-vim
<https://github.com/derekelkins/agda-vim>`_).

To edit a module in Emacs (assuming you have :ref:`installed
<installation>` Agda and the Emacs mode properly), open a file ending
in ``.agda`` and load it by pressing ``C-c C-l`` (other commands are
listed under :ref:`notation-for-key-combinations` below). This will
apply syntax highlighting to the code and display any errors in a
separate buffer. Agda uses certain background colors to indicate
specific issues with the code, see :ref:`highlight` below.


Menus
=====
There are two main menus in the system:

* A main menu called **Agda2** which is used for global commands.

* A context sensitive menu which appears if you right-click in a hole.

The menus contain more commands than the ones listed above. See
:ref:`global <emacs-global-commands>` and :ref:`context sensitive
<emacs-context-sensitive-commands>` commands.


Configuration
=============

If you want to you can customise the Emacs mode. Just start Emacs and
type the following:

.. code-block:: emacs

  M-x load-library RET agda2-mode RET
  M-x customize-group RET agda2 RET

If you want some specific settings for the Emacs mode you can add them
to ``agda2-mode-hook``. For instance, if you do not want to use the
Agda input method (for writing various symbols like ∀≥ℕ→π⟦⟧) you can
add the following to your *.emacs*:

.. code-block:: emacs

  (add-hook 'agda2-mode-hook
            '(lambda ()
              ; If you do not want to use any input method:
              (deactivate-input-method)
              ; (In some versions of Emacs you should use
              ; inactivate-input-method instead of
              ; deactivate-input-method.)

Note that, on some systems, the Emacs mode changes the default font of
the current frame in order to enable many Unicode symbols to be
displayed. This only works if the right fonts are available, though.
If you want to turn off this feature, then you should customise the
``agda2-fontset-name`` variable.

The colors that are used to highlight Agda syntax and errors can be
adjusted by typing ``M-x customize-group RET agda2-highlight RET`` in
Emacs and following the instructions.


Keybindings
===========

.. _notation-for-key-combinations:

Notation for key combinations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following notation is used when describing key combinations:

:kbd:`C-c`
     means hitting the ``c`` key while pressing the ``Ctrl``
     key.

:kbd:`M-x`
     means hitting the ``x`` key while pressing the ``Meta``
     key, which is called ``Alt`` on many systems. Alternatively one
     can type ``Escape`` followed by ``x`` (in separate key strokes).

:kbd:`RET`
     is the ``Enter``, ``Return`` or ``⏎`` key.

:kbd:`SPC`
     is the space bar.

Commands working with terms or types can be prefixed with ``C-u`` to compute without further
normalisation, with ``C-u C-u`` to compute normal forms, and ``C-u C-u C-u`` to compute
weak-head normal forms.

.. _emacs-global-commands:

Global commands
~~~~~~~~~~~~~~~

:kbd:`C-c C-l`
     **L**\ oad file. This type-checks the contents of the file, and
     replaces each occurrence of a question mark ``?`` or a hole
     marker ``{! !}`` by a freshly created hole.

:kbd:`C-c C-x C-c`
     **C**\ ompile file. This will compile an Agda program with a
     ``main`` function using a given backend (the ``GHC`` backend is
     used by default).

:kbd:`C-c C-x C-q`
     **Q**\ uit, kill the Agda process

:kbd:`C-c C-x C-r`
     Kill and **r**\ estart the Agda process

:kbd:`C-c C-x C-a`
     **A**\ bort a command

:kbd:`C-c C-x C-d`
     Remove goals and highlighting (**d**\ eactivate)

:kbd:`C-c C-x C-h`
     Toggle display of **h**\ idden arguments

:kbd:`C-c C-x C-i`
     Toggle display of **i**\ rrelevant arguments

:kbd:`C-c C-=`
     Show constraints

:kbd:`C-c C-s`
     **S**\ olve constraints

:kbd:`C-c C-?`
     Show all goals

:kbd:`C-c C-f`
     Move to next goal (**f**\ orward)

:kbd:`C-c C-b`
     Move to previous goal (**b**\ ackwards)

:kbd:`C-c C-d`
     Infer (**d**\ educe) type. The system asks for a term and infers
     its type.  When executed inside a hole, it will instead take the
     contents of the hole as input (if any).

:kbd:`C-c C-o`
     M\ **o**\ dule c\ **o**\ ntents

:kbd:`C-c C-z`
     :ref:`search-about`

:kbd:`C-c C-n`
     Compute **n**\ ormal form. The system asks for a term which is
     then evaluated. When executed inside a hole, it will instead take
     the contents of the hole as input (if any).

:kbd:`C-u C-c C-n`
     Compute normal form, ignoring ``abstract``

:kbd:`C-u C-u C-c C-n`
     Compute and print normal form of ``show <expression>``

:kbd:`C-c C-x M-;`
     Comment/uncomment rest of buffer

:kbd:`C-c C-x C-s`
     Switch to a different Agda version

.. _emacs-context-sensitive-commands:

Commands in context of a goal
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Commands expecting input (for example which variable to case split)
will either use the text inside the goal or ask the user for input.

:kbd:`C-c C-SPC`
     Give (fill goal)

:kbd:`C-c C-r`
     **R**\ efine. Checks whether the return type of the expression
     ``e`` in the hole matches the expected type. If so, the hole is
     replaced by ``e { }1 ... { }n``, where a sufficient number of new
     holes have been inserted. If the hole is empty, then the refine
     command instead inserts a lambda or constructor (if there is a
     unique type-correct choice).

:kbd:`C-c C-m`
     Elaborate and Give (fill goal with normalized expression).
     Takes the same ``C-u`` prefixes as ``C-c C-n``.

:kbd:`C-c C-a`
     :ref:`auto`

:kbd:`C-c C-c`
     **C**\ ase split. If the cursor is positioned in a hole which
     denotes the right hand side of a definition, then this command
     automatically performs pattern matching on variables of your
     choice. When given several variables (separated by spaces) it
     will case split on the first and then continue by case splitting
     on the remaining variables in each newly created clause. When
     given no variables, it will introduce a new variable if the
     target type is a function type, or introduce a new copattern
     match if the target type is a record type (see
     :ref:`copatterns`). When given the special symbol ``.``, it will
     expand the ellipsis ``...`` in the clause (see
     :ref:`with-abstraction`).

:kbd:`C-c C-h`
     Compute type of **h**\ elper function and add type
     signature to kill ring (clipboard)

:kbd:`C-c C-t`
     Goal **t**\ ype

:kbd:`C-c C-e`
     Context (**e**\ nvironment)

:kbd:`C-c C-d`
     Infer (**d**\ educe) type

:kbd:`C-c C-,`
     Goal type and context. Shows the goal type, i.e. the type
     expected in the current hole, along with the types of locally
     defined identifiers.

:kbd:`C-c C-.`
     Goal type, context and inferred type

:kbd:`C-c C-;`
     Goal type, context and checked term

:kbd:`C-c C-o`
     M\ **o**\ dule c\ **o**\ ntents

:kbd:`C-c C-n`
     Compute **n**\ ormal form

:kbd:`C-u C-c C-n`
     Compute normal form, ignoring ``abstract``

:kbd:`C-u C-u C-c C-n`
     Compute and print normal form of ``show <expression>``

:kbd:`C-c C-w`
     Why in scope, given a defined name returns how it was brought into scope and its definition

Other commands
~~~~~~~~~~~~~~

:kbd:`TAB`
     Indent current line, cycles between points

:kbd:`S-TAB`
     Indent current line, cycles in opposite direction

:kbd:`M-.`
     Go to definition of identifier under point

:guilabel:`Middle mouse button`
     Go to definition of identifier clicked on

:kbd:`C-u M-.`
     Go to definition of a prompted identifier

:kbd:`M-?`
     Query a list of references in loaded files

:kbd:`C-M-.`
     Query a list of identifiers that match a prompt.  The prompt may
     consist of multiple words that can occur in any order or a
     regular expression.

:kbd:`M-,`
     Go back to previous location

.. _unicode-input:

Unicode input
=============

How can I write Unicode characters using Emacs?
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The Agda Emacs mode comes with an input method for easily writing
Unicode characters. Most Unicode character can be input by typing
their corresponding TeX/LaTeX commands, eg. typing ``\lambda`` will
input ``λ``. Some characters have key bindings which have not been
taken from TeX/LaTeX (typing ``\bN`` results in ``ℕ`` being inserted,
for instance), but all bindings start with ``\``.

To see all characters you can input using the Agda input method type
``M-x describe-input-method RET Agda`` or type ``M-x
agda-input-show-translations RET RET`` (with some exceptions in
certain versions of Emacs).

If you know the Unicode name of a character you can input it using
``M-x ucs-insert RET`` (which supports tab-completion) or ``C-x 8
RET``. Example: Type ``C-x 8 RET not SPACE a SPACE sub TAB RET`` to
insert the character "NOT A SUBSET OF" (``⊄``).

(The Agda input method has one drawback: if you make a mistake while
typing the name of a character, then you need to start all over
again. If you find this terribly annoying, then you can use `Abbrev
mode
<https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Abbreviation>`_
instead. However, note that Abbrev mode cannot be used in the
minibuffer, which is used to give input to many Agda and Emacs
commands.)

The Agda input method can be customised via ``M-x customize-group RET
agda-input``.

OK, but how can I find out what to type to get the ... character?
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To find out how to input a specific character, eg from the standard
library, position the cursor over the character and type ``M-x
describe-char`` or ``C-u C-x =``.

For instance, for ``∷`` I get the following:

.. code-block:: none

              character: ∷ (displayed as ∷) (codepoint 8759, #o21067, #x2237)
      preferred charset: unicode (Unicode (ISO10646))
  code point in charset: 0x2237
                 script: symbol
                 syntax: w      which means: word
               category: .:Base, c:Chinese
               to input: type "\::" with Agda input method
            buffer code: #xE2 #x88 #xB7
              file code: #xE2 #x88 #xB7 (encoded by coding system utf-8-unix)
                display: by this font (glyph code)
      x:-misc-fixed-medium-r-normal--20-200-75-75-c-100-iso10646-1 (#x2237)

  Character code properties: customize what to show
    name: PROPORTION
    general-category: Sm (Symbol, Math)
    decomposition: (8759) ('∷')

  There are text properties here:
    fontified            t

Here it says that I can type ``\::`` to get a ``∷``. If there is no
"to input" line, then you can add a key binding to the Agda input
method by using ``M-x customize-variable RET
agda-input-user-translations``.

Show me some commonly used characters
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Many common characters have a shorter input sequence than the
corresponding TeX command:

- **Arrows**: ``\r-`` for ``→``. You can replace ``r`` with another
  direction: ``u``, ``d``, ``l``. Eg. ``\d-`` for ``↓``. Replace
  ``-`` with ``=`` or ``==`` to get a double and triple arrows.
- **Greek letters** can be input by ``\G`` followed by the
  first character of the letters Latin name. Eg. ``\Gl`` will input
  ``λ`` while ``\GL`` will input ``Λ``.
- **Negation**: you can get the negated form of many characters by
  appending ``n`` to the name. Eg. while ``\ni`` inputs ``∋``,
  ``\nin`` will input ``∌``.
- **Subscript** and **superscript**: you can input subscript or
  superscript forms by prepending the character with ``\_`` (subscript)
  or ``\^`` (superscript). Eg. ``g\_1`` will input ``g₁``. Note that not
  all characters have a subscript or superscript counterpart in Unicode.

Note: to introduce multiple characters involving greek letters, subscripts
or superscripts, you need to prepend ``\G``, ``\_`` or ``\^`` respectively
before each character.

Some characters which were used in this documentation or which are
commonly used in the standard library (sorted by hexadecimal code):

========  =========  =================  ===========
Hex code  Character  Short key-binding  TeX command
========  =========  =================  ===========
00AC      ``¬``                         ``\neg``
00D7      ``×``      ``\x``             ``\times``
02E2      ``ˢ``      ``\^s``
03BB      ``λ``      ``\Gl``            ``\lambda``
041F      ``П``
0432      ``в``
0435      ``е``
0438      ``и``
043C      ``м``
0440      ``р``
0442      ``т``
1D62      ``ᵢ``      ``\_i``
2032      ``′``      ``\'1``            ``\prime``
207F      ``ⁿ``      ``\^n``
2081      ``₁``      ``\_1``
2082      ``₂``      ``\_2``
2083      ``₃``      ``\_3``
2084      ``₄``      ``\_4``
2096      ``ₖ``      ``\_k``
2098      ``ₘ``      ``\_m``
2099      ``ₙ``      ``\_n``
========  =========  =================  ===========


========  =========  =================  ===========
Hex code  Character  Short key-binding  TeX command
========  =========  =================  ===========
2113      ``ℓ``                         ``\ell``
========  =========  =================  ===========


========  =========  =================  ===========
Hex code  Character  Short key-binding  TeX command
========  =========  =================  ===========
2115      ``ℕ``      ``\bN``            ``\Bbb{N}``
2191      ``↑``      ``\u``             ``\uparrow``
2192      ``→``      ``\r-``            ``\to``
21A6      ``↦``      ``\r-|``           ``\mapsto``
2200      ``∀``      ``\all``           ``\forall``
2208      ``∈``                         ``\in``
220B      ``∋``                         ``\ni``
220C      ``∌``      ``\nin``
2218      ``∘``      ``\o``             ``\circ``
2237      ``∷``      ``\::``
223C      ``∼``      ``\~``             ``\sim``
2248      ``≈``      ``\~~``            ``\approx``
2261      ``≡``      ``\==``            ``\equiv``
2264      ``≤``      ``\<=``            ``\le``
2284      ``⊄``      ``\subn``
228E      ``⊎``      ``\u+``            ``\uplus``
2294      ``⊔``      ``\lub``
22A2      ``⊢``      ``\|-``            ``\vdash``
22A4      ``⊤``                         ``\top``
22A5      ``⊥``                         ``\bot``
266D      ``♭``       ``\b``
266F      ``♯``       ``\#``
27E8      ``⟨``       ``\<``
27E9      ``⟩``       ``\>``
========  =========  =================  ===========


========  =========  =================  ===========
Hex code  Character  Short key-binding  TeX command
========  =========  =================  ===========
2983      ``⦃``      ``\{{``
2984      ``⦄``      ``\}}``
2985      ``⦅``      ``\((``
2986      ``⦆``      ``\))``
========  =========  =================  ===========


========  =========  =================  ===========
Hex code  Character  Short key-binding  TeX command
========  =========  =================  ===========
2C7C      ``ⱼ``       ``\_j``
========  =========  =================  ===========

.. _highlight:

Background highlighting
=======================

Agda uses various background colors to indicate specific errors or
warnings in your code. Specifically, the following colors are used:

- A *yellow* background indicates unsolved metavariables (see
  :ref:`metavariables`) or unsolved constraints.

- A *light salmon* (pink-orange) background indicates an issue with termination or
  productivity checking (see :ref:`termination-checking`).

- A *wheat* (light yellow) background indicates an issue with coverage
  checking (see :ref:`coverage-checking`).

- A *peru* (brown) background indicates an issue with positivity checking (see
  :ref:`positivity-checking`).

- An *orange* background indicates a type signature with a missing definition.

- A *light coral* (darker pink) background indicates a fatal warning

- A *grey* background indicates unreachable or dead code, and for
  shadowed variable names in telescopes.

- A *white smoke* (light grey) background indicates a clauses that
  does not hold definitionally (see :ref:`case-trees`).

- A *pink* background indicates an issue with confluence checking of
  rewrite rules (see :ref:`confluence-check`).
