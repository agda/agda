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
<../../../src/data/Agda.css>` (use the ``--css`` option).

You can also highlight all the occurrences of the symbol your mouse is
hovering in the HTML by adding the ``--highlight-occurrences`` option.
The default behaviour only highlight the single symbol your mouse is
hovering. Note that this feature may cause browser performance problem,
please enable it carefully (not recommended for huge files).

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

:samp:`--html-dir={directory}`
  Changes the directory where the output is placed to
  :samp:`{directory}`. Default: ``html``.

:samp:`--css={URL}`
  The CSS_ file used by the HTML files (:samp:`{URL}` can be relative).

:samp:`--html-highlight=[code,all,auto]`
  Highlight Agda code only or everything in the generated HTML files.
  Default: ``all``.

.. _CSS:  https://www.w3.org/Style/CSS/
