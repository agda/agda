.. _installation:

************
Installation
************

Debian / Ubuntu
---------------

Prebuilt packages are available for Debian testing/unstable and Ubuntu from Karmic onwards. To install:

.. code-block:: bash

  apt-get install agda-mode

This should install Agda and the Emacs mode.

The standard library is available in Debian testing/unstable and Ubuntu from Lucid onwards. To install:

.. code-block:: bash

  apt-get install agda-stdlib

Fedora
------

Agda is packaged in Fedora (since before Fedora 18).

.. code-block:: bash

  yum install Agda

will pull in emacs-agda-mode and ghc-Agda-devel.

NixOS
-----

Agda is part of the Nixpkgs collection that is used by http://nixos.org/nixos. To install Agda, type:

.. code-block:: bash

  nix-env -iA haskellPackages.Agda

If you’re just interested in the library, you can also install the library without the executable.
Neither the emacs mode nor the Agda standard library are currently installed automatically, though.
