
.. _cabal-flags:

********************
Cabal flag reference
********************

When building Agda from source, the following flags can be used:

.. option:: debug

     Enable debug printing. This makes Agda slightly slower, and
     building Agda slower as well. The :option:`--verbose={N}` option
     only has an effect when Agda was installed with this flag.
     Default: off.

.. option:: debug-serialisation

     Enable debug mode in serialisation. This makes serialisation slower.
     Default: off.

.. option:: debug-parsing

     Enable debug mode in the parser. This makes parsing slower.
     Default: off.

.. option:: dump-core

     Save GHC Core output during compilation of Agda.
     Default: off.

.. option:: enable-cluster-counting

     Enable :ref:`cluster counting <grapheme-clusters>`.
     This will require the `text-icu Haskell library <https://hackage.haskell.org/package/text-icu>`_,
     which in turn requires that the `ICU C library <https://icu.unicode.org/>`_ be installed.
     Note that if ``enable-cluster-counting`` is ``False``, then option
     :option:`--count-clusters` triggers an error message when given to Agda.
     Default: off, but on for development version.

.. option:: optimise-heavily

     Optimise Agda heavily. If this flag is on, compiling Agda uses more memory
     but Agda runs faster.
     Default: on.

.. option:: use-xdg-data-home

    .. versionadded:: 2.8.0

    Install data files under ``$XDG_DATA_HOME/agda/$AGDA_VERSION`` by default
    instead of the installation location defined by Cabal;
    see :option:`--print-agda-data-dir`.
    This should *not* be enabled in declarative build environments like Nix or Guix.
    Default: off.

.. hint:: You can set these flags as follows:

    * With cabal-install, use the ``-f`` argument:

          cabal install -fenable-cluster-counting

    * With stack, use ``--flag`` and an ``Agda:`` prefix:

          stack install --flag Agda:enable-cluster-counting

    * With nix, code into your ``.nix`` scripts using ``enableCabalFlag``:

          hlib.enableCabalFlag "debug" hpkgs.Agda-base
