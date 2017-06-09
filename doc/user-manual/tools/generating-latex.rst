.. _generating-latex:

****************
Generating LaTeX
****************

An experimental LaTeX-backend was added in Agda 2.3.2. It can be used
as follows:

.. code-block:: console

  $ agda --latex {file}.lagda
  $ cd latex
  $ {latex-compiler} {file}.tex

where :samp:`{latex-compiler}` could be :program:`pdflatex`,
:program:`xelatex` or :program:`lualatex`, and :samp:`{file}.lagda` is a
:ref:`literate Agda TeX file <literate-agda-tex>`. The source file
must import the agda latex package by including the line
``\usepackage{agda}``.  Only the top-most module is processed, like
with lhs2tex but unlike with the :ref:`HTML-backend
<generating-html>`. If you want to process imported modules you have
to call ``agda --latex`` manually on each of those modules.

The latex-backend checks if :file:`agda.sty` is found by the latex
environment. If it isn't, a default :file:`agda.sty` is copied from
Agda’s data directory into the working directory (and thus made
available to the latex environment). Colors, fonts, spacing etc can be
modified by editing :file:`agda.sty` and putting it somewhere where
the latex environment can find it.

.. _unicode-latex:

Unicode and LaTeX
-----------------

LaTeX does not by default understand the UTF-8 character encoding. You
can tell LaTeX to treat the input as UTF-8 using the ucs_ package by
inserting the following code in the preamble of your source file:

.. code-block:: latex

   \usepackage{ucs}
   \usepackage[utf8x]{inputenc}

Unicode characters are translated to LaTeX commands, so e.g. the
following packages might be needed. You may need more packages if you
use more unicode characters:

.. code-block:: latex

   \usepackage{amssymb}
   \usepackage{bbm}
   \usepackage[greek,english]{babel}

The ucs package does not contain definitions for all Unicode
characters. If LaTeX complains about a missing definition for some
character U+xxxx, then you can define it yourself:

.. code-block:: latex

   \DeclareUnicodeCharacter{"xxxx}{<definition>}

It may also be necessary to instruct LaTeX to use a specific font
encoding. The autofe package (from the ucs_ bundle) tries to select
the font encoding automatically:

.. code-block:: latex

   \usepackage{autofe}

A :ref:`complete LaTeX template <complete-latex-template>` can be
found below.

.. note::
   LaTeX was never written with unicode in mind. Hacks like the ucs
   package makes it possible to use them, but for the best possible
   output consider using :program:`xelatex` or :program:`lualatex`
   instead. If you do, :file:`agda.sty` is using the more complete
   XITS_ font by default.

Features
--------

Hiding code
~~~~~~~~~~~

Code that you do not want to show up in the output can be hidden using
the LaTeX command ``\AgdaHide``:

.. code-block:: lagda

   \AgdaHide{
   \begin{code}
   -- the code here will not be part of the final document
   \end{code}
   }

``\AgdaHide`` also eats trailing whitespace.

Alignment
~~~~~~~~~

Two or more spaces can be used to make the backend align code, as in
the following example:

.. code-block:: lagda

   \begin{code}
   data ℕ : Set where
     zero  : ℕ
     suc   : ℕ → ℕ

   _+_ : ℕ → ℕ → ℕ
   zero   + n = n
   suc m  + n = suc (m + n)
   \end{code}

In more detail, the constraint on the indentation of the first token
*t* on a line is determined as follows:

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
then the constraint may not be satisfied unless (say) the ``AgdaAlign``
environment is used in an appropriate way. If custom settings are
used, for instance if ``\AgdaIndent`` is redefined, then the constraint
discussed above may not be satisfied.

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

Vertical space around code
~~~~~~~~~~~~~~~~~~~~~~~~~~

Code blocks are by default surrounded by vertical space. Use
``\AgdaNoSpaceAroundCode{}`` to avoid this vertical space, and
``\AgdaSpaceAroundCode{}`` to reenable it.

Note that, if ``\AgdaNoSpaceAroundCode{}`` is used, then empty lines
before or after a code block will not necessarily lead to empty lines
in the generated document. However, empty lines inside the code block
do (by default) lead to empty lines in the output.


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
   \AgdaHide{
   \begin{code}
     hidden
   \end{code}}
   \begin{code}
     visible
   \end{code}
   \end{AgdaAlign}

However, the result may be ugly: extra space is perhaps inserted
around the code blocks. The ``AgdaSuppressSpace`` environment ensures
that extra space is only inserted before the first code block, and
after the last one (but not if ``\AgdaNoSpaceAroundCode{}`` is
used). The environment takes one argument, the number of wrapped code
blocks (excluding hidden ones). Example usage:

.. code-block:: latex

   \begin{AgdaAlign}
   \begin{code}
     code
       more code
   \end{code}
   Explanation...
   \begin{AgdaSuppressSpace}{2}
   \begin{code}
     aligned with "code"
       aligned with "more code"
   \end{code}
   \AgdaHide{
   \begin{code}
     hidden code
   \end{code}}
   \begin{code}
       also aligned with "more code"
   \end{code}
   \end{AgdaSuppressSpace}
   \end{AgdaAlign}

Note that ``AgdaSuppressSpace`` environments should not be nested.  There
is also a combined environment, ``AgdaMultiCode``, that combines the
effects of ``AgdaAlign`` and ``AgdaSuppressSpace``.

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

Typesetting inline code
~~~~~~~~~~~~~~~~~~~~~~~

The backend only typesets code inside code blocks; inline code has
to be typeset manually, e.g.:

.. code-block:: lagda

   Below we postulate a set called \AgdaDatatype{apa}.

   \begin{code}
     postulate apa : Set
   \end{code}

You can find all the commands used by the backend (and which you can
use manually) in the :file:`latex/agda.sty` file. If you are doing a
lot of manual typesetting, then you might want to introduce shorter
command names, e.g.:

.. code-block:: latex

   \newcommand{\D}{\AgdaDatatype}
   \newcommand{\F}{\AgdaFunction}

etc. Long names were chosen by default to avoid name clashes.

.. _latex-inline-references:

Semi-automatically typesetting inline code (experimental)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Since Agda version 2.4.2 there is experimental support for
semi-automatically typesetting code inside text, using the
``references`` option. After loading the agda package with this
option, inline Agda snippets will be typeset in the same way as code
blocks --- after post-processing --- if referenced using the
``\AgdaRef`` command. Only the current module is used; should you
need to reference identifiers in other modules, then you need to
specify which other module manually by using
``\AgdaRef[module]{identifier}``.

In order for the snippets to be typeset correctly, they need to be
post-processed by the :program:`postprocess-latex.pl` script from the
Agda data directory. You can copy it into the current directory by
issuing the command

.. code-block:: console

   $ cp $(dirname $(dirname $(agda-mode locate)))/postprocess-latex.pl .

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


Emulating %format rules
~~~~~~~~~~~~~~~~~~~~~~~

The LaTeX-backend has no feature analogue to :program:`lhs2TeX`'s
``%format`` rules, however most systems come with :program:`sed` which can
be used to achieve similar goals. Given a file called, for example,
:file:`replace.sed`, containing:

.. code-block:: none

   # Super- and subscripts.
   #s/\\textasciicircum\([^\}]*\)‿\([^\}]*\)/\$\^\\AgdaFontStyle\{\\scriptscriptstyle \1\}\_\\AgdaFontStyle\{\\scriptscriptstyle \2\}\$/g

   s/\\textasciicircum\([^\}]*\)/\{\^\\AgdaFontStyle\{\\scriptscriptstyle \1\}\}/g

   #s/‿\([^\}]*\)/\$\_\\AgdaFontStyle\{\\scriptscriptstyle \1\}\$/g

   # Σ[ x ∈ X ] into (x : X) ×
   s/\\AgdaRecord{Σ\[} \(.*\) \\AgdaRecord{∈} \(.*\) \\AgdaRecord{]}/\\AgdaSymbol\{(\}\1 \\AgdaSymbol\{:\} \2\\AgdaSymbol\{)\} \\AgdaFunction\{×\}/g

   # Bind, Kleisli extension and fmap.
   #s/>>=/\$\\mathbin\{>\\!\\!\\!>\\mkern-6.7mu=\}\$/g
   s/>>=/\\mathbin\{>\\!\\!\\!>\\mkern-6.7mu=\}/g
   #s/>>/\$\\mathbin\{>\\!\\!\\!>}\$/g
   #s/=<</\$\\mathbin\{=\\mkern-6.7mu<\\!\\!\\!<\}\$/g
   #s/<\\$>/\$\\mathop\{<\\!\\!\\!\\$\\!\\!\\!>\}\$/g
   s/<\\$>/\\mathop\{<\\!\\!\\!\\$\\!\\!\\!>\}/g

   # Append.
   s/++/+\\!+/g

   # Comments.
   #s/AgdaComment{\-\-/AgdaComment\{\-\\!\-/g

We can postprocess the tex output as follows:

.. code-block:: console

   $ sed -f replace.sed {file}.tex > {file}.sedded
   $ mv {file}.sedded {file}.tex

Note that the above sed file assumes the use of
:program:`{xe|lua}latex` where code is in math mode rather than text
mode (as is the case when using the :program:`pdflatex` compiler). The
commented out variants of the substitution rules are their pdflatex
equivalents.

The substitution rules dealing with super- and subscripts lets us
write ``apa^bepa`` in the code for things we want superscripted in the
output (``\undertie`` does the same for subscripts).


Including Agda code into a larger LaTeX document
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Sometimes you might want to include a bit of code without necessarily
making the whole document a literate Agda file. Here is how to do this
in the context of a beamer presentation, but the method should work
similarly also for other documents. Given two files
:file:`Presentation.tex` and :file:`Code.lagda` as follows:

.. code-block:: latex
   :caption: Presentation.tex

   \documentclass{beamer}

   % When using XeLaTeX, the following should be used instead:
   % \documentclass[xetex]{beamer}
   % \usefonttheme[onlymath]{serif}

   \usepackage{latex/agda}
   \usepackage{catchfilebetweentags}

   \begin{document}
   \begin{frame}\frametitle{Some Agda code}

     \begin{itemize}
       \item The natural numbers
     \end{itemize}

     \ExecuteMetaData[latex/Code.tex]{nat}

     \begin{itemize}
       \item Addition (\AgdaFunction{\_+\_})
     \end{itemize}

     \ExecuteMetaData[latex/Code.tex]{plus}

   \end{frame}
   \end{document}



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

we can use :command:`pdflatex` to compile a presentation as follows:

.. code-block:: console

   $ agda --latex Code.lagda
   $ latexmk -pdf -use-make Presentation.tex

If you are using a lot of unicode it might be more convenient to use
:command:`xelatex` instead. See comments about :command:`xelatex` in
:file:`Presentation.tex` and compile as follows:

.. code-block:: console

  $ agda --latex Code.lagda
  $ latexmk -xelatex -pdf -use-make Presentation.tex

The ``\ExecuteMetaData`` command is part of the catchfilebetweentags_
package. Also see the following `thread on the mailing list
<http://comments.gmane.org/gmane.comp.lang.agda/6195>`_ for other
methods of including Agda code into a presentation.


.. _latex-backend-options:

Options
-------

The following command-line options change the behaviour of the LaTeX
backend:

:samp:`--latex-dir={directory}`
  Changes the output directory where :file:`agda.sty` and the output :file:`.tex` are placed to :samp:`{directory}`. Default: ``latex``.

``--only-scope-checking``
  Generates highlighting without typechecking the file. See
  :ref:`quickLaTeX`.

``--count-clusters``
  Count extended grapheme clusters when generating LaTeX code.
  See :ref:`grapheme-clusters`.


The following options can be given when loading ``agda.sty`` by using
:samp:`\usepackage[{options}]{agda}`:

``bw``
  Colour scheme which highlights in black and white.

``conor``
  Colour scheme similar to the colours used in Epigram1.

``references``
  Enables :ref:`inline typesetting <latex-inline-references>` of
  referenced code.

``links``
  Enables :ref:`hyperlink support <latex-links>`.

.. _grapheme-clusters:

Counting Extended Grapheme Clusters
-----------------------------------

The alignment feature regards the string ``+̲``, containing ``+`` and a
combining character, as having length two. However, it seems more
reasonable to treat it as having length one, as it occupies a single
column, if displayed "properly" using a monospace font. The new flag
``--count-clusters`` is an attempt at fixing this. When this flag is
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
correct, but if ``--count-clusters`` is used, then the LaTeX backend
does not align the two field keywords:

::

  record +̲ : Set₁ where  field A : Set
                          field B : Set

The ``--count-clusters`` flag is not enabled in all builds of Agda,
because the implementation depends on the ICU_ library, the
installation of which could cause extra trouble for some users. The
presence of this flag is controlled by the Cabal flag
``enable-cluster-counting``.

.. _quickLaTeX:

Quicker generation without typechecking
---------------------------------------

A faster variant of the backend is available by invoking
``QuickLaTeX`` from the Emacs mode, or using ``agda --latex
--only-scope-checking``.  When this variant of the backend is used the
top-level module is not type-checked, only scope-checked. This implies
that some highlighting information is not available. For instance,
overloaded constructors are not resolved.

If the module has already been type-checked successfully, then this
information is reused; in this case QuickLaTeX behaves like the
regular LaTeX backend.

Known issues
------------

.. COMMENT: update this when a new version of Debian comes out

The unicode-math package and older versions of the polytable package
(still in the Debian stable) are incompatible, which can result in
`errors in generated latex code
<https://github.com/kosmikus/lhs2tex/issues/29>`_. The workaround is
to download a more up to date version of polytable_ and either put it
with the generated files, or install it globally.

.. _complete-latex-template:

Complete LaTeX Template for Literate Agda with Unicode
-------------------------------------------------------

This template has been tested under Debian and Ubuntu with TexLive,
but should also work in other distributions. For :program:`xelatex` or
:program:`lualatex`, only ``\usepackage{agda}`` should be needed.

.. code-block:: latex

   \documentclass{article}

   \usepackage{agda}

   % The following packages are needed because unicode
   % is translated (using the next set of packages) to
   % latex commands. You may need more packages if you
   % use more unicode characters:

   \usepackage{amssymb}
   \usepackage{bbm}
   \usepackage[greek,english]{babel}

   % This handles the translation of unicode to latex:

   \usepackage{ucs}
   \usepackage[utf8x]{inputenc}
   \usepackage{autofe}

   % Some characters that are not automatically defined
   % (you figure out by the latex compilation errors you get),
   % and you need to define:

   \DeclareUnicodeCharacter{8988}{\ensuremath{\ulcorner}}
   \DeclareUnicodeCharacter{8989}{\ensuremath{\urcorner}}
   \DeclareUnicodeCharacter{8803}{\ensuremath{\overline{\equiv}}}

   % Add more as you need them (shouldn't happen often).

   \begin{document}

   \begin{code}
    -- your Agda code goes here
   \end{code}

   \end{document}

.. _ucs: https://www.ctan.org/pkg/ucs
.. _polytable: https://www.ctan.org/pkg/polytable
.. _hyperref: https://www.ctan.org/pkg/hyperref
.. _XITS: http://www.ctan.org/tex-archive/fonts/xits/
.. _catchfilebetweentags: https://www.ctan.org/pkg/catchfilebetweentags
.. _ICU: http://site.icu-project.org/
