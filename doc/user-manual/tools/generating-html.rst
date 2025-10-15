.. _generating-html:

***************
Generating HTML
***************

To generate highlighted, hyperlinked web pages from source code, run
the following command in a shell:

.. code-block:: console

   $ agda --html --html-dir={output directory} {root module}

You can change the way in which the code is highlighted by providing
your own CSS file instead of the :download:`default, included one
<../../../src/data/html/Agda.css>` (use the :option:`--css` option).

.. note::

  The :file:`Agda.css` shipped with Agda is located at
  :file:`html/Agda.css` in the Agda data directory.
  Since version 2.6.2, the
  Agda data directory can be printed using the option
  :option:`--print-agda-dir`, which has been an alias of
  :option:`--print-agda-data-dir` since 2.6.4.1.
  Thus, you can get hold of the CSS file via
  :samp:`cat $(agda --print-agda-data-dir)/html/Agda.css`.

You can also get highlighting for all occurrences of the symbol the mouse pointer is
hovering over in the HTML by adding the :option:`--highlight-occurrences` option.
The default behaviour is to only highlight the single symbol under the mouse pointer.

If you're using Literate Agda with Markdown or reStructedText and you
want to highlight your Agda codes with Agda's HTML backend and render
the rest of the content (let's call it "literate" part for convenience)
with some another renderer, you can use the ``--html-highlight=code``
option, which makes the Agda compiler:

- not wrapping the literate part into ``<a class="Background">`` tags
- not wrapping the generated document with a ``<html>`` tag,
  which means you'll have to specify the CSS location somewhere else,
  like ``<link rel="stylesheet" type="text/css" href="Agda.css">``
- converting ``<a class="Markup">`` tags into
  ``<pre class="agda-code">`` tags that wrap the complete Agda code
  block below
- generating files with extension as-is (i.e. `.lagda.md` becomes
  `.md`, `.lagda.rst` becomes `.rst`)
- for reStructuredText, a ``.. raw:: html`` will be inserted
  before every code blocks

This will affect all the files involved in one compilation, making
pure Agda code files rendered without HTML footer/header as well.
To use ``code`` with literate Agda files and ``all`` with pure Agda
files, use ``--html-highlight=auto``, which means auto-detection.

Options
-------

:option:`--html`

  Generate HTML files with highlighted source code.

.. option:: --html-dir={DIR}

     Set directory in which HTML files are placed to ``DIR``
     (default: ``html``).

.. option:: --html-highlight=[code,all,auto]

     .. versionadded:: 2.6.0

     Whether to highlight non-Agda code as comments in generated HTML
     files (default: ``all``).

.. option:: --css={URL}

     Set URL of the CSS_ file used by the HTML files to ``URL``
     (can be relative).

.. option:: --highlight-occurrences

     .. versionadded:: 2.6.2

     When :ref:`generating HTML <generating-html>`,
     place the :file:`highlight-hover.js` script
     in the output directory (see :option:`--html-dir`).
     In the presence of the script,
     hovering over an identifier in the rendering of the HTML
     will highlight all occurrences of the same identifier on the page.

.. _CSS:  https://www.w3.org/Style/CSS/
