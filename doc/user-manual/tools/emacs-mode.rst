.. _emacs-mode:

**********
Emacs Mode
**********

.. note::
   This is a stub.


Keybindings
===========

Commands working with types can be prefixed with ``C-u`` to compute
type without further normalisation and with ``C-u C-u`` to compute
normalised types.

.. _emacs-global-commands:

Global commands
~~~~~~~~~~~~~~~

===================  =========================================================
``C-c C-l``          **L**\ oad file
``C-c C-x C-c``      **C**\ ompile file
``C-c C-x C-q``      **Q**\ uit, kill the Agda process
``C-c C-x C-r``      Kill and **r**\ estart the Agda process
``C-c C-x C-d``      Remove goals and highlighting (**d**\ eactivate)
``C-c C-x C-h``      Toggle display of **h**\ idden arguments
``C-c C-=``          Show constraints
``C-c C-s``          **S**\ olve constraints
``C-c C-?``          Show all goals
``C-c C-f``          Move to next goal (**f**\ orward)
``C-c C-b``          Move to previous goal (**b**\ ackwards)
``C-c C-d``          Infer (**d**\ educe) type
``C-c C-o``          M\ **o**\ dule c\ **o**\ ntents
``C-c C-z``          Search through definitions in scope
``C-c C-n``          Compute **n**\ ormal form
``C-u C-c C-n``      Compute normal form, ignoring ``abstract``
``C-u C-u C-c C-n``  Compute and print normal form of ``show <expression>``
``C-c C-x M-;``      Comment/uncomment rest of buffer
===================  =========================================================

Commands in context of a goal
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Commands expecting input (for example which variable to case split)
will either use the text inside the goal or ask the user for input.

===================  =========================================================
``C-c C-SPC``        Give (fill goal)
``C-c C-r``          **R**\ efine. Partial give: makes new holes for
                     missing arguments
``C-c C-a``          :ref:`auto`
``C-c C-c``          **C**\ ase split
``C-c C-h``          Compute type of **h**\ elper function and add
                     type signature to kill ring (clipboard)
``C-c C-t``          Goal **t**\ ype
``C-c C-e``          Context (**e**\ nvironment)
``C-c C-d``          Infer (**d**\ educe) type
``C-c C-,``          Goal type and context
``C-c C-.``          Goal type, context and inferred type
``C-c C-o``          M\ **o**\ dule c\ **o**\ ntents
``C-c C-n``          Compute **n**\ ormal form
``C-u C-c C-n``      Compute normal form, ignoring ``abstract``
``C-u C-u C-c C-n``  Compute and print normal form of ``show <expression>``
===================  =========================================================

Other commands
~~~~~~~~~~~~~~

====================  =================================================
``TAB``               Indent current line, cycles between points
``S-TAB``             Indent current line, cycles in opposite direction
 ``M-.``              Go to definition of identifier under point
 Middle mouse button  Go to definition of identifier clicked on
 ``M-*``              Go back
====================  =================================================

.. _unicode-input:

Unicode input
=============

The Agda emacs mode comes with an input method for for easily writing
Unicode characters. Most Unicode character can be input by typing
their corresponding TeX or LaTeX commands, eg. typing ``\lambda`` will
input ``λ``. To see all characters you can input using the Agda input
method see ``M-x describe-input-method Agda``.

If you know the Unicode name of a character you can input it using
``M-x ucs-insert`` or ``C-x 8 RET``. Example: ``C-x 8 RET not SPACE a
SPACE sub TAB RET`` to insert "NOT A SUBSET OF" ``⊄``.

To find out how to input a specific character, eg from the standard
library, position the cursor over the character and use ``M-x
describe-char`` or ``C-u C-x =``.

The Agda input method can be customised via ``M-x customize-group
agda-input``.


Common characters
~~~~~~~~~~~~~~~~~

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
  or ``\^`` (superscript). Note that not all characters have a
  subscript or superscript counterpart in Unicode.

Some characters which were used in this documentation or which are
commonly used in the standard library (sorted by hexadecimal code):

========  =========  =================  ===========
Hex code  Character  Short key-binding  TeX command
========  =========  =================  ===========
00ac      ``¬``                         ``\neg``
00d7      ``×``      ``\x``             ``\times``
02e2      ``ˢ``      ``\^s``
03bb      ``λ``      ``\Gl``            ``\lambda``
041f      ``П``
0432      ``в``
0435      ``е``
0438      ``и``
043c      ``м``
0440      ``р``
0442      ``т``
1d62      ``ᵢ``      ``\_i``
2032      ``′``      ``\'1``            ``\prime``
207f      ``ⁿ``      ``\^n``
2081      ``₁``      ``\_1``
2082      ``₂``      ``\_2``
2083      ``₃``      ``\_3``
2084      ``₄``      ``\_4``
2096      ``ₖ``      ``\_k``
2098      ``ₘ``      ``\_m``
2099      ``ₙ``      ``\_n``
========  =========  =================  ===========


========  ================  =================  ===========
Hex code  Character         Short key-binding  TeX command
========  ================  =================  ===========
2113      ``ℓ`` (PDF TODO)                     ``\ell``
========  ================  =================  ===========


========  =========  =================  ===========
Hex code  Character  Short key-binding  TeX command
========  =========  =================  ===========
2115      ``ℕ``      ``\bn``            ``\Bbb{N}``
2192      ``→``      ``\r-``            ``\to``
21a6      ``↦``      ``\r-|``           ``\mapsto``
2200      ``∀``      ``\all``           ``\forall``
2208      ``∈``                         ``\in``
220b      ``∋``                         ``\ni``
220c      ``∌``      ``\nin``
2218      ``∘``      ``\o``             ``\circ``
2237      ``∷``      ``\::``
223c      ``∼``      ``\~``             ``\sim``
2248      ``≈``      ``\~~``            ``\approx``
2261      ``≡``      ``\==``            ``\equiv``
2264      ``≤``      ``\<=``            ``\le``
2284      ``⊄``      ``\subn``
2294      ``⊔``      ``\lub``
22a2      ``⊢``      ``\|-``            ``\vdash``
22a4      ``⊤``                         ``\top``
22a5      ``⊥``                         ``\bot``
266d      ``♭``       ``\b``
266f      ``♯``       ``\#``
27e8      ``⟨``       ``\<``
27e9      ``⟩``       ``\>``
========  =========  =================  ===========


========  ================  =================  ===========
Hex code  Character         Short key-binding  TeX command
========  ================  =================  ===========
2983      ``⦃`` (PDF TODO)   ``\{{``
2984      ``⦄`` (PDF TODO)   ``\}}``
========  ================  =================  ===========


========  =========  =================  ===========
Hex code  Character  Short key-binding  TeX command
========  =========  =================  ===========
2c7c      ``ⱼ``       ``\_j``
========  =========  =================  ===========
