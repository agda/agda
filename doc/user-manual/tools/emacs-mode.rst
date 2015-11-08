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


Global commands
~~~~~~~~~~~~~~~

+-------------------------+-------------------------------------------------+
|``C-c C-l``              |**L**\ oad file                                  |
+-------------------------+-------------------------------------------------+
|``C-c C-x C-c``          |**C**\ ompile file                               |
+-------------------------+-------------------------------------------------+
|``C-c C-x C-q``          |**Q**\ uit, kill the Agda process                |
+-------------------------+-------------------------------------------------+
|``C-c C-x C-r``          |Kill and **r**\ estart the Agda process          |
+-------------------------+-------------------------------------------------+
|``C-c C-x C-d``          |Remove goals and highlighting (**d**\ eactivate) |
|                         |                                                 |
+-------------------------+-------------------------------------------------+
|``C-c C-x C-h``          |Toggle display of **h**\ idden arguments         |
+-------------------------+-------------------------------------------------+
|``C-c C-=``              |Show constraints                                 |
+-------------------------+-------------------------------------------------+
|``C-c C-s``              |**S**\ olve constraints                          |
+-------------------------+-------------------------------------------------+
|``C-c C-?``              |Show all goals                                   |
+-------------------------+-------------------------------------------------+
|``C-c C-f``              |Move to next goal (**f**\ orward)                |
+-------------------------+-------------------------------------------------+
|``C-c C-b``              |Move to previous goal (**b**\ ackwards)          |
+-------------------------+-------------------------------------------------+
|``C-c C-d``              |Infer (**d**\ educe) type                        |
|                         |                                                 |
+-------------------------+-------------------------------------------------+
|``C-c C-o``              |M\ **o**\ dule c\ **o**\ ntents                  |
+-------------------------+-------------------------------------------------+
|``C-c C-n``              |Compute **n**\ ormal form                        |
+-------------------------+-------------------------------------------------+
|``C-u C-c C-n``          |Compute normal form, ignoring ``abstract``       |
|                         |                                                 |
+-------------------------+-------------------------------------------------+
|``C-c C-x M-;``          |Comment/uncomment rest of buffer                 |
+-------------------------+-------------------------------------------------+


Commands in context of a goal
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Commands expecting input (for example which variable to case split)
will either use the text inside the goal or ask the user for input.

+-------------------------+--------------------------------------------------------+
|``C-c C-SPC``            |Give (fill goal)                                        |
+-------------------------+--------------------------------------------------------+
|``C-c C-r``              |**R**\ efine. Partial give: makes new holes for missing |
|                         |arguments                                               |
+-------------------------+--------------------------------------------------------+
|``C-c C-a``              |:ref:`auto`                                             |
+-------------------------+--------------------------------------------------------+
|``C-c C-c``              |**C**\ ase split                                        |
+-------------------------+--------------------------------------------------------+
|``C-c C-h``              |Compute type of **h**\ elper function and add type      |
|                         |signature to kill ring (clipboard)                      |
+-------------------------+--------------------------------------------------------+
|``C-c C-t``              |Goal **t**\ ype                                         |
+-------------------------+--------------------------------------------------------+
|``C-c C-e``              |Context (**e**\ nvironment)                             |
+-------------------------+--------------------------------------------------------+
|``C-c C-d``              |Infer (**d**\ educe) type                               |
+-------------------------+--------------------------------------------------------+
|``C-c C-,``              |Goal type and context                                   |
+-------------------------+--------------------------------------------------------+
|``C-c C-.``              |Goal type, context and inferred type                    |
+-------------------------+--------------------------------------------------------+
|``C-c C-o``              |M\ **o**\ dule c\ **o**\ ntents                         |
+-------------------------+--------------------------------------------------------+
|``C-c C-n``              |Compute **n**\ ormal form                               |
+-------------------------+--------------------------------------------------------+
|``C-u C-c C-n``          |Compute normal form, ignoring ``abstract``              |
|                         |                                                        |
+-------------------------+--------------------------------------------------------+


Other commands
~~~~~~~~~~~~~~

+-------------------------+----------------------------------------+
|``TAB``                  |Indent current line, cycles between     |
|                         |points                                  |
+-------------------------+----------------------------------------+
|``S-TAB``                |Indent current line, cycles in opposite |
|                         |direction                               |
+-------------------------+----------------------------------------+
|``M-.``                  |Go to definition of identifier under    |
|                         |point                                   |
+-------------------------+----------------------------------------+
|Middle mouse button      |Go to definition of identifier clicked  |
|                         |on                                      |
+-------------------------+----------------------------------------+
|``M-*``                  |Go back                                 |
+-------------------------+----------------------------------------+



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

Some characters which are commonly used in the standard library:

+-----------+--------------------+--------------------+
|Character  |Short key-binding   |TeX command         |
+===========+====================+====================+
|→          |``\r-``             |``\to``             |
+-----------+--------------------+--------------------+
|₁          |``\_1``             |                    |
+-----------+--------------------+--------------------+
|₂          |``\_2``             |                    |
+-----------+--------------------+--------------------+
|≈          |``\~~``             |``\approx``         |
+-----------+--------------------+--------------------+
|∀          |``\all``            |``\forall``         |
+-----------+--------------------+--------------------+
|⟨          |``\<``              |                    |
+-----------+--------------------+--------------------+
|⟩          |``\>``              |                    |
+-----------+--------------------+--------------------+
|ℓ          |                    |``\ell``            |
+-----------+--------------------+--------------------+
|≡          |``\==``             |``\equiv``          |
+-----------+--------------------+--------------------+
|∼          |``\~``              |``\sim``            |
+-----------+--------------------+--------------------+
|≤          |``\<=``             |``\le``             |
+-----------+--------------------+--------------------+
|′          |``\'1``             |``\prime``          |
+-----------+--------------------+--------------------+
|∷          |``\::``             |                    |
+-----------+--------------------+--------------------+
|λ          |``\Gl``             |``\lambda``         |
+-----------+--------------------+--------------------+
|¬          |                    |``\neg``            |
+-----------+--------------------+--------------------+
|∘          |``\o``              |``\circ``           |
+-----------+--------------------+--------------------+
|ℕ          |``\bn``             |``\Bbb{N}``         |
+-----------+--------------------+--------------------+
|×          |``\x``              |``\times``          |
+-----------+--------------------+--------------------+
