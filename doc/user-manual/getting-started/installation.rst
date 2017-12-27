.. _installation:

************
Installation
************

Arch Linux
----------

The following prebuilt packages are available:

* `Agda <https://www.archlinux.org/packages/community/x86_64/agda/>`_

* `Agda standard library <https://www.archlinux.org/packages/community/x86_64/agda-stdlib/>`_

Debian / Ubuntu
---------------

Prebuilt packages are available for Debian testing/unstable and Ubuntu from Karmic onwards. To install:

.. code-block:: bash

  apt-get install agda-mode

This should install Agda and the Emacs mode.

The standard library is available in Debian testing/unstable and Ubuntu from Lucid onwards. To install:

.. code-block:: bash

  apt-get install agda-stdlib

More information:

* `Agda (Debian) <https://tracker.debian.org/pkg/agda>`_

* `Agda standard library (Debian) <https://tracker.debian.org/pkg/agda-stdlib>`_

* `Agda (Ubuntu) <https://launchpad.net/ubuntu/+source/agda|Agda>`_

* `Agda standard library (Ubuntu) <https://launchpad.net/ubuntu/+source/agda-stdlib>`_

Reporting bugs:

Please report any bugs to Debian, using:

.. code-block:: bash

  reportbug -B debian agda
  reportbug -B debian agda-stdlib

Fedora
------

Agda is packaged in Fedora (since before Fedora 18).

.. code-block:: bash

  yum install Agda

will pull in emacs-agda-mode and ghc-Agda-devel.

FreBSD
------

Packages are available from `FreshPorts
<https://www.freebsd.org/cgi/ports.cgi?query=agda&stype=all>`_ for
Agda and Agda standard library.


NixOS
-----

Agda is part of the Nixpkgs collection that is used by http://nixos.org/nixos. To install Agda and agda-mode for Emacs, type:

.. code-block:: bash

  nix-env -f "<nixpkgs>" -iA haskellPackages.Agda

If you’re just interested in the library, you can also install the library without the executable. The Agda standard library is currently not installed automatically.

OS X
----

`Homebrew <http://brew.sh>`_ provides prebuilt packages for OS X.  To install:

.. code-block:: bash

  brew install agda

This should take less than a minute, and install Agda together with the Emacs mode and the standard library.

By default, the standard library is installed in ``/usr/local/lib/agda/``.  To use the standard library, it is convenient to add ``/usr/local/lib/agda/standard-library.agda-lib`` to ``~/.agda/libraries``, and specify ``standard-library`` in ``~/.agda/defaults``.  Note this is not performed automatically.

It is also possible to install ``--without-stdlib``, ``--without-ghc``, or from ``--HEAD``.  Note this will require building Agda from source.

For more information, refer to the `Homebrew documentation <http://git.io/brew-docs>`_.
