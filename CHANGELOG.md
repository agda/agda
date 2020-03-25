Release notes for Agda version 2.6.2
====================================

Pragmas and options
-------------------

* New options `--qualified-instances` (default) and
  `--no-qualified-instances`. When `--no-qualified-instances` is
  enabled, Agda will only consider candidates for instance search that
  are in scope under an unqualified name (see
  [#4522](https://github.com/agda/agda/pull/4522)).

* New option `--call-by-name` turns off call-by-need evaluation at type
  checking time.

* New option `--highlight-occurrences` (off by default) enables the HTML
  backend to include a JavaScript file that highlights all occurrences of
  the mouse-hovered symbol (see
  [#4535](https://github.com/agda/agda/pull/4535)).

