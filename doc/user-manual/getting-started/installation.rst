.. _installation:

************
Installation
************

There are several ways to install Agda:

* Using a :ref:`released source <installation-from-hackage>` package
  from `Hackage <https://hackage.haskell.org/package/Agda>`_

* Using a :ref:`binary package <prebuilt-packages>` prepared for your
  platform

* Using the :ref:`development version
  <installation-development-version>` from the Git `repository
  <https://github.com/agda/agda>`_

Agda can be installed using different flags (see :ref:`installation-flags`).

.. _installation-from-hackage:

Installation from Hackage
=========================

You can install the latest released version of Agda from `Hackage
<https://hackage.haskell.org/package/Agda>`_. Install the
:ref:`prerequisites <prerequisites>` and then run the following
commands:

.. code-block:: bash

  cabal update
  cabal install Agda
  agda-mode setup

The last command tries to set up Emacs for use with Agda via the
:ref:`Emacs mode <emacs-mode>`. As an alternative you can copy the
following text to your *.emacs* file:

.. code-block:: emacs

  (load-file (let ((coding-system-for-read 'utf-8))
                  (shell-command-to-string "agda-mode locate")))

It is also possible (but not necessary) to compile the Emacs mode's
files:

.. code-block:: bash

  agda-mode compile

This can, in some cases, give a noticeable speedup.

**Warning**: If you reinstall the Agda mode without recompiling the
Emacs Lisp files, then Emacs may continue using the old, compiled
files.


.. _prebuilt-packages:

Prebuilt Packages and System-Specific Instructions
==================================================

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

* `Agda (Ubuntu) <https://launchpad.net/ubuntu/+source/agda>`_

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

FreeBSD
-------

Packages are available from `FreshPorts
<https://www.freebsd.org/cgi/ports.cgi?query=agda&stype=all>`_ for
Agda and Agda standard library.


NixOS
-----

Agda is part of the Nixpkgs collection that is used by
https://nixos.org/nixos. To install Agda and agda-mode for Emacs,
type:

.. code-block:: bash

  nix-env -f "<nixpkgs>" -iA haskellPackages.Agda

If you’re just interested in the library, you can also install the
library without the executable. The Agda standard library is currently
not installed automatically.

OS X
----

`Homebrew <https://brew.sh>`_ provides prebuilt packages for OS X.  To install:

.. code-block:: bash

  brew install agda

This should take less than a minute, and install Agda together with
the Emacs mode and the standard library.

By default, the standard library is installed in
``/usr/local/lib/agda/``.  To use the standard library, it is
convenient to add ``/usr/local/lib/agda/standard-library.agda-lib`` to
``~/.agda/libraries``, and specify ``standard-library`` in
``~/.agda/defaults``.  Note this is not performed automatically.

It is also possible to install ``--without-stdlib``,
``--without-ghc``, or from ``--HEAD``.  Note this will require
building Agda from source.

For more information, refer to the `Homebrew documentation
<https://docs.brew.sh/>`_.

.. NOTE::

   If Emacs cannot find the ``agda-mode`` executable, it might help to
   install the exec-path-from-shell_ package by doing ``M-x
   package-install RET exec-path-from-shell RET``, and adding

   .. code-block:: elisp

     (exec-path-from-shell-initialize)

   to your ``.emacs`` file.

.. _installation-development-version:

Installation of the Development Version
=======================================

After getting the development version following the instructions in
the `Agda wiki <http://wiki.portal.chalmers.se/agda/pmwiki.php>`_:

* Install the :ref:`prerequisites <prerequisites>`

* In the top-level directory of the Agda source tree

  * Follow the :ref:`instructions <installation-from-hackage>` for
    installing Agda from Hackage (except run ``cabal install``
    instead of ``cabal install Agda``) or

  * You can try to install Agda (including a compiled Emacs mode) by
    running the following command:

    .. code-block:: bash

      make install

    Note that on a Mac, because ICU is installed in a non-standard location,
    you need to specify this location on the command line:

    .. code-block:: bash

      make install-bin CABAL_OPTS='--extra-lib-dirs=/usr/local/opt/icu4c/lib --extra-include-dirs=/usr/local/opt/icu4c/include'

.. _installation-flags:

Installation Flags
==================

When installing Agda the following flags can be used:

:samp:`cpphs`
   Use `cpphs <https://hackage.haskell.org/package/cpphs>`_ instead of
   cpp. Default: off.

:samp:`debug`
   Enable debugging features that may slow Agda down. Default: off.

:samp:`flag enable-cluster-counting`
   Enable the ``--count-clusters`` flag (see
   :ref:`grapheme-clusters`). Note that if ``enable-cluster-counting``
   is ``False``, then the ``--count-clusters`` flag triggers an error
   message. Default: off.

.. _exec-path-from-shell: https://github.com/purcell/exec-path-from-shell
