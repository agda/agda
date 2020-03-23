Release notes for Agda version 2.6.2
====================================


Pragmas and options
-------------------

* New options `--qualified-instances` (default) and
  `--no-qualified-instances`. When `--no-qualified-instances` is
  enabled, Agda will only consider candidates for instance search that
  are in scope under an unqualified name (see
  [#4522](https://github.com/agda/agda/pull/4522)).
