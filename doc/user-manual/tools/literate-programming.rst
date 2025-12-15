.. _literate-programming:

********************
Literate Programming
********************

Agda supports a limited form of literate programming, i.e. code
interspersed with prose, if the corresponding filename extension is
used.

.. _literate-agda-tex:

Literate TeX
------------

Files ending in :file:`.lagda` or :file:`.lagda.tex` are interpreted
as literate TeX_ files. All code has to appear in code blocks:

.. code-block:: lagda

   Ignored by Agda.

   \begin{code}[ignored by Agda]
   module Whatever where
   -- Agda code goes here
   \end{code}

Text outside of code blocks is ignored, as well as text right after
``\begin{code}``, on the same line.

Agda finds code blocks by looking for the first instance of
``\begin{code}`` that is not preceded on the same line by ``%`` or
``\`` (not counting ``\`` followed by any code point), then (starting
on the next line) the first instance of ``\end{code}`` that is
preceded by nothing but spaces or tab characters (``\t``), and so on
(always starting on the next line). Note that Agda does not try to
figure out if, say, the LaTeX code changes the category code of ``%``.

If you provide a suitable definition for the code environment, then
literate Agda files can double as LaTeX document sources. Example
definition:

.. code-block:: latex

   \usepackage{fancyvrb}

   \DefineVerbatimEnvironment
     {code}{Verbatim}
     {} % Add fancy options here if you like.

The :ref:`LaTeX backend <generating-latex>` or the preprocessor
lhs2TeX_ can also be used to produce LaTeX code from literate Agda
files. See :ref:`unicode-latex` for how to make LaTeX accept Agda
files using the UTF-8 character encoding.

Literate reStructuredText
-------------------------

Files ending in :file:`.lagda.rst` are interpreted as literate
reStructuredText_ files. Agda will parse code following a line ending
in ``::``, as long as that line does not start with ``..``:

.. code-block:: rst

   This line is ordinary text, which is ignored by Agda.

   ::

     module Whatever where
     -- Agda code goes here

   Another non-code line.
   ::
   .. This line is also ignored

reStructuredText source files can be turned into other formats such as
HTML or LaTeX using Sphinx_.

* Code blocks inside an rST comment block will be type-checked by
  Agda, but not rendered.

* Code blocks delimited by ``.. code-block:: agda`` or
  ``.. code-block:: lagda`` will be rendered, but not type-checked by
  Agda.

* All lines inside a codeblock must be further indented than the first
  line of the code block.

* Indentation must be consistent between code blocks. In other words,
  the file as a whole must be a valid Agda file if all the literate
  text is replaced by white space.

Literate Markdown and Typst
---------------------------

Files ending in :file:`.lagda.md` are interpreted as literate
Markdown_ files, while files ending in :file:`.lagda.typ` are
interpreted as literate Typst_ files. They use the same syntax
for code blocks, and they are parsed the same way by Agda.
Code blocks start with ``````` or `````agda`` on
its own line, and end with ```````, also on its own line:

.. code-block:: md

   This line is ordinary text, which is ignored by Agda.

   ```
   module Whatever where
   -- Agda code goes here
   ```

   Here is another code block:

   ```agda
   data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ
   ```

For Typst, Agda does not yet support highlighting the code blocks.

Markdown source files can be turned into many other formats such as
HTML or LaTeX using PanDoc_.

* Code blocks which should be type-checked by Agda but should not be
  visible when the Markdown is rendered may be enclosed in HTML
  comment delimiters (``<!--`` and ``-->``).

* Code blocks which should be ignored by Agda, but rendered in the
  final document may be indented by four spaces.

* Note that inline code fragments are not supported due to the
  difficulty of interpreting their indentation level with respect to
  the rest of the file.

.. _literate-markdown-only-agda-blocks:

Only ``agda`` code blocks
~~~~~~~~~~~~~~~~~~~~~~~~~

.. versionadded:: 2.9.0

By default, both unmarked code blocks (```````) and explicitly
marked code blocks (`````agda``) are treated as Agda code.

With the :option:`--literate-markdown-only-agda-blocks` command-line option
(off by default), only code blocks explicitly marked with `````agda`` are
treated as Agda code. Unmarked code blocks are treated as verbatim text and
are not type-checked. This allows including other code examples in the
document without Agda attempting to parse them.

Example with ``--literate-markdown-only-agda-blocks``:

.. code-block:: md

   This is prose.

   Here is some Agda code:

   ```agda
   data Bool : Set where
     true false : Bool
   ```

   Here is a JavaScript example that is NOT type-checked:

   ```
   function hello() { return "world"; }
   ```

   Here is another verbatim block with a language tag:

   ```haskell
   main = putStrLn "Hello, World!"
   ```

This option is not available as pragma since it affects parsing before any pragma options are processed.
It must be set via command line (``agda --literate-markdown-only-agda-blocks``)
or passed under ``flags:`` in the ``.agda-lib`` file.


Literate Org
------------

Files ending in :file:`.lagda.org` are interpreted as literate
Org_ files. Code blocks are surrounded by two lines including only
```#+begin_src agda2``` and ```#+end_src``` (case-insensitive).

.. code-block:: text

    This line is ordinary text, which is ignored by Agda.

    #+begin_src agda2
    module Whatever where
    -- Agda code goes here
    #+end_src

    Another non-code line.

* Code blocks which should be ignored by Agda, but rendered in the
  final document may be placed in source blocks without the ``agda2``
  label.

Literate Forester
-----------------

Files ending in :file:`.lagda.tree` are interpreted as literate
Forester_ files. Literate forester uses ```\agda{...}``` for code blocks.

  * ``agda --html --html-highlight=code example.lagda.tree`` will produce the file ``html/example.tree``.
  * These produced trees ``html/*.tree`` are valid, hence add ``html/`` to ``forest.toml`` as trees.
  * Add ``html/`` to ``forest.toml`` as assets.
  * Modify ``theme/tree.xsl`` of your forester project, adding ``Agda.css`` to the linked styles.

Running ``forester build`` should now produce file ``example.xml`` with Agda syntax highlighting.

.. code-block:: text

   \p{This line is ordinary text, which is ignored by Agda.}

   \agda{
   module Whatever where
   -- Agda code goes here
   }

   \p{Here is another code block:}

   \agda{
   data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ
   }

.. _TeX: http://tug.org/
.. _reStructuredText: http://docutils.sourceforge.io/rst.html
.. _Markdown: https://daringfireball.net/projects/markdown/
.. _Org: https://orgmode.org
.. _Typst: https://typst.app
.. _Forester: https://sr.ht/~jonsterling/forester/

.. _lhs2TeX: https://www.andres-loeh.de/lhs2tex/
.. _agda-tree: https://github.com/dannypsnl/agda-tree
.. _Sphinx: http://www.sphinx-doc.org/en/stable/
.. _Pandoc: https://pandoc.org/
