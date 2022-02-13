.. _generating-latex:

****************
Generating LaTeX
****************

An experimental LaTeX backend was added in Agda 2.3.2. It can be used
as follows:

.. code-block:: console

  $ agda --latex {file}.lagda
  $ cd latex
  $ {latex-compiler} {file}.tex

where :samp:`{latex-compiler}` could be :program:`pdflatex`,
:program:`xelatex` or :program:`lualatex`, and :samp:`{file}.lagda` is
a :ref:`literate Agda TeX file <literate-agda-tex>` (it could also be
called :samp:`{file}.lagda.tex`). The source file is expected to
import the LaTeX package ``agda`` by including the code
``\usepackage{agda}`` (possibly with some options). Unlike the
:ref:`HTML backend <generating-html>` only the top-most module is
processed. Imported modules can be processed by invoking
``agda --latex`` manually on each of them.

The LaTeX backend checks if :file:`agda.sty` is found by the LaTeX
environment. If it isn't, a default :file:`agda.sty` is copied into
the LaTeX output directory (by default :file:`latex`). Note that the
appearance of typeset code can be modified by overriding definitions
from :file:`agda.sty`.

.. note::

  The :file:`agda.sty` shipped with Agda is located at
  :file:`{${AGDA_DIR}}/latex/agda.sty`.  Since version 2.6.2, the
  :envvar:`AGDA_DIR` is printed by option :option:`--print-agda-dir`.
  Thus, you can get hold of the CSS file via
  :samp:`cat $(agda --print-agda-dir)/latex/agda.sty`.

.. _unicode-latex:

Known pitfalls and issues
-------------------------

* Unicode characters may not be typeset properly out of the box. How
  to address this problem depends on what LaTeX engine is used.

  * pdfLaTeX:

    The pdfLaTeX program does not by default understand the UTF-8
    character encoding. You can tell it to treat the input as UTF-8 by
    using the inputenc package:

    .. code-block:: latex

       \usepackage[utf8]{inputenc}

    If the inputenc package complains that some Unicode character is
    "not set up for use with LaTeX", then you can give your own
    definition. Here is one example:

    .. code-block:: latex

      \usepackage{newunicodechar}
      \newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
      \newunicodechar{←}{\ensuremath{\mathnormal\from}}
      \newunicodechar{→}{\ensuremath{\mathnormal\to}}
      \newunicodechar{∀}{\ensuremath{\mathnormal\forall}}

  * XeLaTeX or LuaLaTeX:

    It can sometimes be easier to use LuaLaTeX or XeLaTeX. When these
    engines are used it might suffice to choose a suitable font, as
    long as it contains all the right symbols in all the right shapes.
    If it does not, then ``\newunicodechar`` can be used as above.
    Here is one example:

    .. code-block:: latex

      \usepackage{unicode-math}
      \setmathfont{XITS Math}

      \usepackage{newunicodechar}
      \newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}

* If ``<`` and ``>`` are typeset like ``¡`` and ``¿``, then the
  problem might be that you are using pdfLaTeX and have not selected a
  suitable font encoding.

  Possible workaround:

  .. code-block:: latex

    \usepackage[T1]{fontenc}

* If a regular text font is used, then ``--`` might be typeset as an
  en dash (–).

  Possible workarounds:

  * Use a monospace font.

  * Turn off ligatures. With pdfLaTeX the following code (which also
    selects a font encoding, and only turns off ligatures for
    character sequences starting with ``-``) might work:

    .. code-block:: latex

      \usepackage[T1]{fontenc}
      \usepackage{microtype}
      \DisableLigatures[-]{encoding=T1}

    With LuaLaTeX or XeLaTeX the following code (which also selects a
    font) might work:

    .. code-block:: latex

      \usepackage{fontspec}
      \defaultfontfeatures[\rmfamily]{}
      \setmainfont{Latin Modern Roman}

    Note that you might not want to turn off all kinds of ligatures in
    the entire document. See the `examples <Examples>`_ below for
    information on how to set up special font families without TeX
    ligatures that are only used for Agda code.

* The unicode-math package and older versions of the polytable package
  are incompatible, which can result in `errors in generated LaTeX
  code <https://github.com/kosmikus/lhs2tex/issues/29>`_.

  Possible workaround: Download a more up-to-date version of
  polytable_ and put it together with the generated files or install
  it globally.

.. _latex-backend-options:

Options
-------

The following command-line options change the behaviour of the LaTeX
backend:

``--latex-dir={directory}``
  Changes the output directory where :file:`agda.sty` and the output
  :file:`.tex` file are placed to :samp:`{directory}`. Default:
  ``latex``.

:option:`--only-scope-checking`
  Generates highlighting without typechecking the file. See
  :ref:`quickLaTeX`.

:option:`--count-clusters`
  Count extended grapheme clusters when generating LaTeX code. This
  option can be given in :ref:`OPTIONS<options-pragma>` pragmas.
  See :ref:`grapheme-clusters`.

The following options can be given when loading ``agda.sty`` by using
``\usepackage[options]{agda}``:

``bw``
  Colour scheme which highlights in black and white.

``conor``
  Colour scheme similar to the colours used in Epigram 1.

``references``
  Enables :ref:`inline typesetting <latex-inline-references>` of
  referenced code.

``links``
  Enables :ref:`hyperlink support <latex-links>`.

.. _quickLaTeX:

Quicker generation without typechecking
---------------------------------------

A faster variant of the backend is available by invoking
``QuickLaTeX`` from the Emacs mode, or using ``agda --latex
--only-scope-checking``. When this variant of the backend is used the
top-level module is not type-checked, only scope-checked. Note that
this can affect the generated document. For instance, scope-checking
does not resolve overloaded constructors.

If the module has already been type-checked successfully, then this
information is reused; in this case QuickLaTeX behaves like the
regular LaTeX backend.

Features
--------

Vertical space
~~~~~~~~~~~~~~

Code blocks are by default surrounded by vertical space. Use
``\AgdaNoSpaceAroundCode{}`` to avoid this vertical space, and
``\AgdaSpaceAroundCode{}`` to reenable it.

Note that, if ``\AgdaNoSpaceAroundCode{}`` is used, then empty lines
before or after a code block will not necessarily lead to empty lines
in the generated document. However, empty lines inside the code block
do (by default, with or without ``\AgdaNoSpaceAroundCode{}``) lead to
empty lines in the output. The height of such empty lines can be
controlled by the length ``\AgdaEmptySkip``, which by default is
``\abovedisplayskip``.

Alignment
~~~~~~~~~

Tokens preceded by two or more space characters, as in the following
example, are aligned in the typeset output:

.. code-block:: lagda

   \begin{code}
   data ℕ : Set where
     zero  : ℕ
     suc   : ℕ → ℕ

   _+_ : ℕ → ℕ → ℕ
   zero   + n = n
   suc m  + n = suc (m + n)
   \end{code}

In the case of the first token on a line a single space character
sometimes suffices to get alignment. A constraint on the indentation
of the first token *t* on a line is determined as follows:

* Let *T* be the set containing every previous token (in any code
  block) that is either the initial token on its line or preceded by
  at least one whitespace character.

* Let *S* be the set containing all tokens in *T* that are not
  *shadowed* by other tokens in *T*. A token *t₁* is shadowed by
  *t₂* if *t₂* is further down than *t₁* and does not start to the
  right of *t₁*.

* Let *L* be the set containing all tokens in *S* that start to the
  left of *t*, and *E* be the set containing all tokens in *S* that
  start in the same column as *t*.

* The constraint is that *t* must be indented further than every
  token in *L*, and aligned with every token in *E*.

Note that if any token in *L* or *E* belongs to a previous code block,
then the constraint may not be satisfied unless (say) the
``AgdaAlign`` :ref:`environment <breaking-up-code-blocks>` is used in
an appropriate way. If custom settings are used, for instance if
``\AgdaIndent`` is redefined, then the constraint discussed above may
not be satisfied.

Examples:

* Here ``C`` is indented further than ``B``:

::

   postulate
      A  B
          C : Set

* Here ``C`` is not (necessarily) indented further than ``B``, because
  ``X`` shadows ``B``:

::

   postulate
      A  B  : Set
      X
          C : Set

These rules are inspired by, but not identical to, the one used by
lhs2TeX's poly mode (see Section 8.4 of the `manual for lhs2TeX
version 1.17 <https://www.andres-loeh.de/lhs2tex/Guide2-1.17.pdf>`_).

.. _grapheme-clusters:

Counting Extended Grapheme Clusters
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The alignment feature regards the string ``+̲``, containing ``+`` and a
combining character, as having length two. However, it seems more
reasonable to treat it as having length one, as it occupies a single
column, if displayed "properly" using a monospace font. The flag
:option:`--count-clusters` is an attempt at fixing this. When this flag is
enabled the backend counts `"extended grapheme clusters"
<http://www.unicode.org/reports/tr29/#Grapheme_Cluster_Boundaries>`_
rather than code points.

Note that this fix is not perfect: a single extended grapheme cluster
might be displayed in different ways by different programs, and might,
in some cases, occupy more than one column. Here are some examples of
extended grapheme clusters, all of which are treated as a single
character by the alignment algorithm:

.. code-block:: lagda

   │ │
   │+̲│
   │Ö̂│
   │நி│
   │ᄀힰᇹ│
   │ᄀᄀᄀᄀᄀᄀힰᇹᇹᇹᇹᇹᇹ│
   │ │

Note also that the layout machinery does not count extended grapheme
clusters, but code points. The following code is syntactically
correct, but if :option:`--count-clusters` is used, then the LaTeX backend
does not align the two field keywords:

::

  record +̲ : Set₁ where  field A : Set
                          field B : Set

The :option:`--count-clusters` flag is not enabled in all builds of Agda,
because the implementation depends on the ICU_ library, the
installation of which could cause extra trouble for some users. The
presence of this flag is controlled by the Cabal flag
``enable-cluster-counting``.

.. _breaking-up-code-blocks:

Breaking up code blocks
~~~~~~~~~~~~~~~~~~~~~~~

Sometimes one might want to break up a code block into multiple
pieces, but keep code in different blocks aligned with respect to each
other. Then one can use the ``AgdaAlign`` environment. Example usage:

.. code-block:: latex

   \begin{AgdaAlign}
   \begin{code}
     code
       code  (more code)
   \end{code}
   Explanation...
   \begin{code}
     aligned with "code"
       code  (aligned with (more code))
  \end{code}
  \end{AgdaAlign}

Note that ``AgdaAlign`` environments should not be nested.

Sometimes one might also want to hide code in the middle of a code
block. This can be accomplished in the following way:

.. code-block:: latex

   \begin{AgdaAlign}
   \begin{code}
     visible
   \end{code}
   \begin{code}[hide]
     hidden
   \end{code}
   \begin{code}
     visible
   \end{code}
   \end{AgdaAlign}

However, the result may be ugly: extra space is perhaps inserted
around the code blocks. The ``AgdaSuppressSpace`` environment ensures
that extra space is only inserted before the first code block, and
after the last one (but not if ``\AgdaNoSpaceAroundCode{}`` is
used). Example usage:

.. code-block:: latex

   \begin{AgdaAlign}
   \begin{code}
     code
       more code
   \end{code}
   Explanation...
   \begin{AgdaSuppressSpace}
   \begin{code}
     aligned with "code"
       aligned with "more code"
   \end{code}
   \begin{code}[hide]
     hidden code
   \end{code}
   \begin{code}
       also aligned with "more code"
   \end{code}
   \end{AgdaSuppressSpace}
   \end{AgdaAlign}

Note that ``AgdaSuppressSpace`` environments should not be nested.  There
is also a combined environment, ``AgdaMultiCode``, that combines the
effects of ``AgdaAlign`` and ``AgdaSuppressSpace``.

Hiding code
~~~~~~~~~~~

Code that you do not want to show up in the output can be hidden by
giving the argument ``hide`` to the code block:

.. code-block:: lagda

   \begin{code}[hide]
   -- the code here will not be part of the final document
   \end{code}

.. _latex-links:

Hyperlinks (experimental)
~~~~~~~~~~~~~~~~~~~~~~~~~

If the hyperref_ latex package is loaded before the agda package and
the ``links`` option is passed to the agda package, then the agda package
provides a function called ``\AgdaTarget``. Identifiers which have been
declared targets, by the user, will become clickable hyperlinks in the
rest of the document. Here is a small example:

.. literalinclude:: ../../../test/LaTeXAndHTML/succeed/Links.lagda
   :language: lagda

The borders around the links can be suppressed using hyperref's
``hidelinks`` option:

.. code-block:: latex

    \usepackage[hidelinks]{hyperref}

.. warning::
   The current approach to links does not keep track of scoping or
   types, and hence overloaded names might create links which point to
   the wrong place. Therefore it is recommended to not overload names
   when using the links option at the moment. This might get fixed in
   the future.

Numbered code listings
~~~~~~~~~~~~~~~~~~~~~~

When the option ``number`` is used an equation number is generated for
the code listing. The number is set to the right, centered vertically.
By default the number is set in parentheses, but this can be changed
by redefining ``\AgdaFormatCodeNumber``.

The option can optionally be given an argument: when ``number=l`` is
used a label ``l``, referring to the code listing, is generated. It is
possible to use this option several times with different labels.

An example:

.. code-block:: lagda

   \begin{code}[number=code:lemma]
     a proof
   \end{code}
   %
   A consequence of Lemma~\ref{code:lemma} is that…

The option ``number`` has no effect if used together with ``hide``,
``inline`` or ``inline*``.

Inline code
~~~~~~~~~~~

Code can be typeset inline by giving the argument ``inline`` to the
code block:

.. code-block:: lagda

  Assume that we are given a type
  %
  \begin{code}[hide]
    module _ (
  \end{code}
  \begin{code}[inline]
      A : Set
  \end{code}
  \begin{code}[hide]
      ) where
  \end{code}
  %
  .

There is also a variant of ``inline``, ``inline*``. If ``inline*`` is
used, then space (``\AgdaSpace{}``) is added at the end of the code,
and when ``inline`` is used space is not added.

The implementation of these options is a bit of a hack. Only use these
options for typesetting a single line of code without multiple
consecutive whitespace characters (except at the beginning of the
line).

Another way to typeset inline code
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

An alternative to using ``inline`` and ``inline*`` is to typeset code
manually. Here is an example:

.. code-block:: lagda

   Below we postulate the existence of a type called
   \AgdaPostulate{apa}:
   %
   \begin{code}
     postulate apa : Set
   \end{code}

You can find all the commands used by the backend (and which you can
use manually) in the :file:`agda.sty` file.

.. _latex-inline-references:

Semi-automatically typesetting inline code (experimental)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Since Agda version 2.4.2 there is experimental support for
semi-automatically typesetting code inside text, using the
``references`` option. After loading the agda package with this
option, inline Agda snippets will be typeset in the same way as code
blocks---after post-processing---if referenced using the ``\AgdaRef``
command. Only the current module is used; should you need to reference
identifiers in other modules, then you need to specify which other
module manually by using ``\AgdaRef[module]{identifier}``.

In order for the snippets to be typeset correctly, they need to be
post-processed by the :program:`postprocess-latex.pl` script from the
Agda data directory. You can copy it into the current directory by
issuing the command

.. code-block:: console

   $ cp $(agda --print-agda-dir)/latex/postprocess-latex.pl .

In order to generate a PDF, you can then do the following:

.. code-block:: console

   $ agda --latex {file}.lagda
   $ cd latex/
   $ perl ../postprocess-latex.pl {file}.tex > {file}.processed
   $ mv {file}.processed {file}.tex
   $ xelatex {file}.tex

Here is a full example, consisting of a Literate Agda file
:file:`Example.lagda` and a makefile :file:`Makefile`.

.. code-block:: lagda
   :caption: Example.lagda

   \documentclass{article}
   \usepackage[references]{agda}

   \begin{document}

   Here we postulate \AgdaRef{apa}.
   %
   \begin{code}
     postulate apa : Set
   \end{code}

   \end{document}

.. code-block:: make
   :caption: Makefile

   AGDA=agda
   AFLAGS=-i. --latex
   SOURCE=Example
   POSTPROCESS=postprocess-latex.pl
   LATEX=latexmk -pdf -use-make -xelatex

   all:
       $(AGDA) $(AFLAGS) $(SOURCE).lagda
       cd latex/ && \
       perl ../$(POSTPROCESS) $(SOURCE).tex > $(SOURCE).processed && \
       mv $(SOURCE).processed $(SOURCE).tex && \
       $(LATEX) $(SOURCE).tex && \
       mv $(SOURCE).pdf ..

See `Issue #1054 on the bug tracker <https://github.com/agda/agda/issues/1054>`_ for implementation details.

.. warning:: Overloading identifiers should be avoided. If multiple
   identifiers with the same name exist, then \AgdaRef will typeset
   according to the first one it finds.

Controlling the typesetting of individual tokens
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The typesetting of (certain) individual tokens can be controlled by
redefining the ``\AgdaFormat`` command. Example:

.. code-block:: latex

   \usepackage{ifthen}

   % Insert extra space before some tokens.
   \DeclareRobustCommand{\AgdaFormat}[2]{%
     \ifthenelse{
       \equal{#1}{≡⟨} \OR
       \equal{#1}{≡⟨⟩} \OR
       \equal{#1}{∎}
     }{\ }{}#2}

Note the use of ``\DeclareRobustCommand``. The first argument to
``\AgdaFormat`` is the token, and the second argument the thing to be
typeset.

Emulating %format rules
~~~~~~~~~~~~~~~~~~~~~~~

The LaTeX backend has no feature directly comparable to lhs2TeX's
``%format`` rules. However, one can hack up something similar by using
a program like :program:`sed`. For instance, let us say that
:file:`replace.sed` contains the following text:

.. code-block:: none

   # Turn Σ[ x ∈ X ] into (x : X) ×.
   s/\\AgdaRecord{Σ\[} \(.*\) \\AgdaRecord{∈} \(.*\) \\AgdaRecord{]}/\\AgdaSymbol\{(\}\1 \\AgdaSymbol\{:\} \2\\AgdaSymbol\{)\} \\AgdaFunction\{×\}/g

The output of the LaTeX backend can then be postprocessed in the
following way:

.. code-block:: console

   $ sed -f replace.sed {file}.tex > {file}.sedded
   $ mv {file}.sedded {file}.tex

Including Agda code in a larger LaTeX document
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Sometimes you might want to include a bit of code without making the
whole document a literate Agda file. There are two ways in which this
can be accomplished.

(The following technique was probably invented by Anton
Setzer.)  Put the code in a separate file, and use ``\newcommand`` to
give a name to each piece of code that should be typeset:

.. code-block:: latex
   :caption: Code.lagda.tex

   \newcommand{\nat}{%
   \begin{code}
   data ℕ : Set where
     zero  : ℕ
     suc   : (n : ℕ) → ℕ
   \end{code}}

Preprocess this file using Agda, and then include it in another file
in the following way:

.. code-block:: latex
   :caption: Main.tex

   % In the preamble:
   \usepackage{agda}
   % Further setup related to Agda code.

   % The Agda code can be included either in the preamble or in the
   % document's body.
   \input{Code}

   % Then one can refer to the Agda code in the body of the text:
   The natural numbers can be defined in the following way in Agda:
   \nat{}

Here it is assumed that :file:`agda.sty` is available in the current
directory (or on the TeX search path).

Note that this technique can also be used to present code in a
different order, if the rules imposed by Agda are not compatible with
the order that you would prefer.

There is another technique that uses the catchfilebetweentags_
latex package. Assuming you have some code in :file:`Code.lagda`
and want to include it in :file:`Paper.tex`, you first add
tags to your code as follows:

 .. code-block:: lagda
   :caption: Code.lagda

   %<*nat>
   \begin{code}
   data ℕ : Set where
     zero  : ℕ
     suc   : (n : ℕ) → ℕ
   \end{code}
   %</nat>

   %<*plus>
   \begin{code}
   _+_ : ℕ → ℕ → ℕ
   zero   + n = n
   suc m  + n = suc (m + n)
   \end{code}
   %</plus>

You can then use ``\ExecuteMetaData``, as provided by
catchfilebetweentags_, to include the code. Note that
the code does not have to be in the same order (or from
the same files).  This method is particularly convenient
when you want to write a paper or presentation about
a library of code.

.. code-block:: latex
   :caption: Paper.tex

   % Other setup related to Agda...
   \usepackage{catchfilebetweentags}

   \begin{document}

     \begin{itemize}
       \item The natural numbers
     \end{itemize}

     \ExecuteMetaData[latex/Code.tex]{nat}

     \begin{itemize}
       \item Addition (\AgdaFunction{\_+\_})
     \end{itemize}

     \ExecuteMetaData[latex/Code.tex]{plus}


Examples
--------

Some examples that can be used for inspiration (in the HTML version of
the manual you see links to the source code and in the PDF version of
the manual you see inline source code).

.. only:: builder_html

   * For the ``article`` class and pdfLaTeX:
     :download:`article-pdflatex.lagda.tex`.

   * For the ``article`` class and LuaLaTeX or XeLaTeX:
     :download:`article-luaxelatex.lagda.tex` if you want to use the default
     fonts (with—at the time of writing—bad coverage of non-ASCII
     characters), and
     :download:`article-luaxelatex-different-fonts.lagda.tex` if you would
     prefer to use other fonts (with possibly better coverage).

   * For the ``beamer`` class and pdfLaTeX:
     :download:`beamer-pdflatex.lagda.tex`.

   * For the ``beamer`` class and LuaLaTeX or XeLaTeX:
     :download:`beamer-luaxelatex.lagda.tex`.

   * For the ``acmart`` class and pdfLaTeX:
     :download:`acmart-pdflatex.lagda.tex`.

   * For the ``acmart`` class and XeLaTeX:
     :download:`acmart-xelatex.lagda.tex`.

.. only:: builder_latex

   * For the ``article`` class and pdfLaTeX:

     .. literalinclude:: article-pdflatex.lagda.tex
        :language: latex

   * For the ``article`` class and LuaLaTeX or XeLaTeX:

     + If you want to use the default fonts (with—at the time of
       writing—bad coverage of non-ASCII characters):

       .. literalinclude:: article-luaxelatex.lagda.tex
          :language: latex

     + If you would prefer to use other fonts (with possibly better
       coverage):

       .. literalinclude:: article-luaxelatex-different-fonts.lagda.tex
          :language: latex

   * For the ``beamer`` class and pdfLaTeX:

     .. literalinclude:: beamer-pdflatex.lagda.tex
        :language: latex

   * For the ``beamer`` class and LuaLaTeX or XeLaTeX:

     .. literalinclude:: beamer-luaxelatex.lagda.tex
        :language: latex

   * For the ``acmart`` class and pdfLaTeX:

     .. literalinclude:: acmart-pdflatex.lagda.tex
        :language: latex

   * For the ``acmart`` class and XeLaTeX:

     .. literalinclude:: acmart-xelatex.lagda.tex
        :language: latex

Note that these examples might not satisfy all your requirements, and
might not work in all settings (in particular, for LuaLaTeX or XeLaTeX
it might be necessary to install one or more fonts). If you have to
follow a particular house style, then you may want to make sure that
the Agda code follows this style, and that you do not inadvertently
change the style of other text when customising the style of the Agda
code.

.. _polytable: https://www.ctan.org/pkg/polytable
.. _hyperref: https://www.ctan.org/pkg/hyperref
.. _catchfilebetweentags: https://www.ctan.org/pkg/catchfilebetweentags
.. _ICU: http://site.icu-project.org/
