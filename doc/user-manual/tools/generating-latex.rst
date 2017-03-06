.. _generating-latex:

****************
Generating LaTeX
****************

Literate Programming
--------------------

Agda supports a limited form of literate programming out of the
box. If you name your source files :file:`Something.lagda`, then all
the code has to appear in code blocks:

.. code-block:: lagda

   \begin{code}
   module Whatever where
   -- ...
   \end{code}

The text outside the code blocks is ignored. If you provide a suitable
definition for the code environment, then literate Agda files can
double as LaTeX document sources. Example definition:

.. code-block:: latex

   \usepackage{verbatim}
   \newenvironment{code}{\verbatim}{\endverbatim}

The preprocessor :program:`lhs2TeX` can also handle literate Agda files.

Unicode and LaTeX
-----------------

LaTeX does not by default understand the UTF-8 character encoding. You
can tell LaTeX to treat the input as UTF-8 by inserting the following
code in the preamble of your source file:

.. code-block:: latex

   \usepackage{ucs}
   \usepackage[utf8x]{inputenc}

The ucs package does not contain definitions for all Unicode
characters. If LaTeX complains about a missing definition for some
character U+xxxx, then you can define it yourself:

.. code-block:: latex

   \DeclareUnicodeCharacter{"xxxx}{<definition>}

It may also be necessary to instruct LaTeX to use a specific font
encoding. The autofe package tries to select the font encoding
automatically:

.. code-block:: latex

   \usepackage{autofe}

(Note that the lhs2TeX support files for Agda already do something
similar to the steps above.)

A complete LaTeX template for literate Agda with Unicode
--------------------------------------------------------

This has been tested under Ubuntu with texlive, but should work in
other distributions:

.. code-block:: latex

   \documentclass{article}

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

   % Using "\newenvironment" to redefine verbatim to
   % be called "code" doesn't always work properly.
   % You can more reliably use:

   \usepackage{fancyvrb}

   \DefineVerbatimEnvironment
     {code}{Verbatim}
     {} % Add fancy options here if you like.

   \begin{document}

   \begin{code}
    -- your Agda code goes here
   \end{code}

   \end{document}

The LaTeX-backend
-----------------

An experimental LaTeX-backend was added in Agda 2.3.2. It can be used
as follows:

.. code-block:: console

  $ agda --latex {file}.lagda
  $ cd latex
  $ {latex-compiler} {file}.tex

where ``{latex-compiler}`` could be :program:`pdflatex`,
:program:`xelatex` or :program:`lualatex`. See the release notes for
versions 2.3.2 and 2.3.4 for further details and examples:
http://code.haskell.org/Agda/CHANGELOG

Making up for the lack of lhs2TeX’s %format rules
-------------------------------------------------

The LaTeX-backend has no feature analogue to :program:`lhs2TeX`'s
%format rule, however most systems come with :program:`sed` which can
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
equivalents (see next section before using them though).

The substitution rules dealing with super- and subscripts lets us
write ``apa^bepa`` in the code for things we want superscripted in the
output (``\undertie`` does the same for subscripts).

Manually typesetting inline code
--------------------------------

The backend only typesets code inside code blocks, inline code you
have to typeset manually, e.g.:

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

Semi-automatically typesetting inline code
------------------------------------------

Since Agda version 2.4.2 there is experimental support for
semi-automatically typesetting code inside text, using the references
option. Here is a full example.

Example.lagda
~~~~~~~~~~~~~

.. code-block:: lagda

   \documentclass{article}
   \usepackage[references]{agda}

   \begin{document}

   Here we postulate \AgdaRef{apa}.

   \begin{code}
     postulate apa : Set
   \end{code}

   \end{document}

Makefile
~~~~~~~~

Note that postprocess-latex.pl can be found in the Agda data dir,
i.e. issue
``cp $(dirname $(dirname $(agda-mode locate)))/postprocess-latex.pl .``
(once) before :command:`make`.

.. code-block:: make

   AGDA=agda
   AFLAGS=-i. --latex
   SOURCE=Example
   POSTPROCESS=postprocess-latex.pl
   LATEX=latexmk -pdf -use-make -e '$$pdflatex=q/xelatex %O %S/'

   all:
       $(AGDA) $(AFLAGS) $(SOURCE).lagda
       cd latex/ && \
       perl ../$(POSTPROCESS) $(SOURCE).tex > $(SOURCE).processed && \
       mv $(SOURCE).processed $(SOURCE).tex && \
       $(LATEX) $(SOURCE).tex && \
       mv $(SOURCE).pdf ..

Implementation details
~~~~~~~~~~~~~~~~~~~~~~

See https://code.google.com/p/agda/issues/detail?id=1054 for
implementation details.

{xe|lua}latex and proper unicode fonts
--------------------------------------

LaTeX was never written with unicode in mind, hacks like the ucs
package makes it possible to use them, but for the best possible
output consider using xelatex or lualatex instead.

The default math font in agda.sty is limited though (many characters
are missing). The XITS font is more complete:

http://www.ctan.org/tex-archive/fonts/xits/

Simply save the .otf files into :file:`~/.fonts`, use:

.. code-block:: latex

   \setmainfont{XITS}
   \setmathfont{XITS Math}

in :file:`agda.sty`, and compile the output using:

.. code-block:: console

   $ latexmk -pdf -e '$pdflatex=q/lualatex %O %S/' {file}.tex

Using Beamer together with the LaTeX-backend to create slides for talks
-----------------------------------------------------------------------

Sometimes you might want to include a bit of code without necessarily
making the whole document a literate Agda file. The following section
describes how to do this in the context of a beamer presentation, but
should work similarly for a document. Given the two files
:file:`Presentation.tex`:

.. code-block:: latex

   \documentclass{beamer}

   % When using XeLaTeX, the following should be used instead:
   % \documentclass[xetex, mathserif, serif]{beamer}
   %
   % The default font in XeLaTeX doesn’t have the default bullet character, so
   % either change the font:
   % \setmainfont{XITS}
   % \setmathfont{XITS Math}
   %
   % Or change the character:
   %\setbeamertemplate{itemize items}{•}

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

and :file:`Code.lagda`:

::

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
  $ latexmk -e '$pdflatex=q/xelatex S/' -pdf -use-make Presentation.tex

With a sufficently new version of :command:`latexmk` one can use
the ``-xelatex-flag`` instead of the ``-e '...'`` stuff.

The ``\ExecuteMetaData`` command is part of the neat catchfilebetweentags
package, which you can read more about here:

http://mirrors.ctan.org/macros/latex/contrib/catchfilebetweentags/catchfilebetweentags.pdf

Also see the following thread on the mailing list for other methods of
including Agda code into a presentation:

http://comments.gmane.org/gmane.comp.lang.agda/6195

“Can we produce a document without doing typechecking every time?”
------------------------------------------------------------------

No, typechecking is essential to the typesetting (otherwise we don’t
know what colours etc to use).

However, since lhs2tex and the latex backend are interchangeable (or
should be at least), I suppose you could have a "fast" and a "slow"
make target, e.g. a Makefile with:

.. code-block:: make

   COMPILER=latexmk -pdf -use-make -e '$$pdflatex=q/xelatex %O %S/'

   fast:
         lhs2tex --agda {file}.lagda > latex/{file}.tex
         cd latex && \
         $(COMPILER) {file}.tex && \
         mv {file}.pdf ..

   slow:
         agda --latex {file}.lagda
         cd latex && \
         $(COMPILER) {file}.tex && \
         mv {file}.pdf ..

Then you can compile using ``make fast`` to avoid typechecking (at the
cost of not having colours etc).

Known issues
------------

unicode-math and (oldish versions of) polytable are incompatible. See
this bug report:

https://github.com/kosmikus/lhs2tex/issues/29

Error messages generated by latex usually look like:
    ! Argument of ... has an extra }.
