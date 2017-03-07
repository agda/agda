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

Options
-------

:samp:`--html-dir {directory}`
  Changes the directory where the output is placed to
  :samp:`{directory}`. Default: ``html``.

:samp:`--css {URL}`
  The CSS_ file used by the HTML files (:samp:`{URL}` can be relative).

.. _CSS:  https://www.w3.org/Style/CSS/
