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

.. hint:: If you want a sneak peek of Agda without installing it, try the
  `Agda Pad <agda-pad_>`_

.. _agda-pad: https://agdapad.quasicoherent.io/

Installation from source
========================

.. _prerequisites:

Step 1 : Prerequisites
----------------------

You need recent versions of the following programs to compile Agda:

* GHC:           https://www.haskell.org/ghc/

  + Agda has been tested with GHC 8.6.5, 8.8.4,
    8.10.7, 9.0.2, 9.2.7, 9.4.5 and 9.6.1.

* cabal-install: https://www.haskell.org/cabal/
* Alex:          https://www.haskell.org/alex/
* Happy:         https://www.haskell.org/happy/
* GNU Emacs:     http://www.gnu.org/software/emacs/

You should also make sure that programs installed by *cabal-install*
are on your shell's search path.
The installation location is described by field ``installdir`` in the cabal configuration
(check ``~/.cabal/config``; it defaults to ``~/.cabal/bin``).
So, e.g. under Ubuntu or macOS, you may need to add

.. code-block:: bash

  export PATH=~/.cabal/bin:$PATH

to your ``.profile`` or ``.bash_profile``.

Non-Windows users need to ensure that the development files for the C
libraries *zlib* and *ncurses* are installed (see http://zlib.net
and http://www.gnu.org/software/ncurses/). Your package manager may be
able to install these files for you. For instance, on Debian or Ubuntu
it should suffice to run

.. code-block:: bash

  apt-get install zlib1g-dev libncurses5-dev

as root to get the correct files installed.

.. _icu-install:

ICU and cluster counting
^^^^^^^^^^^^^^^^^^^^^^^^

Optionally one can also install the `ICU <http://site.icu-project.org>`_ library,
which is used to implement the :option:`--count-clusters` option.
Once the ICU library is installed and configured,
one can enable the :option:`--count-clusters` option
by giving the :option:`enable-cluster-counting` flag to *cabal install*:

.. code-block:: bash

  cabal install -f enable-cluster-counting

Information on installing the ICU prerequisite on various OSs is available at
https://github.com/haskell/text-icu/blob/master/README.markdown#prerequisites
(retrieved 2022-02-09).

- Under Debian or Ubuntu it may suffice to install ``libicu-dev``.

- Under macOS, try ``brew install icu4c``.
  Note that this installs ICU in a non-standard location.
  You may need to set

  .. code-block:: bash

    export PKG_CONFIG_PATH="$(brew --prefix)/opt/icu4c/lib/pkgconfig"

  See ``brew info icu4c`` for details.


Step 2 : Installing the ``agda`` and the ``agda-mode`` programs
---------------------------------------------------------------

After installing the :ref:`prerequisites <prerequisites>` you can
install the latest released version of Agda from `Hackage
<https://hackage.haskell.org/package/Agda>`_.

Using ``cabal``
^^^^^^^^^^^^^^^

For installing the ``agda`` and the ``agda-mode`` programs using
``cabal`` run the following commands:

.. code-block:: bash

  cabal update
  cabal install Agda

If you use `Nix-style Local Builds
<https://cabal.readthedocs.io/en/3.4/nix-local-build-overview.html>`_,
by using Cabal ≥ 3.0 or by running ``cabal v2-install``, you'll get the
following error when compiling with the GHC backend::

  Compilation error:

  MAlonzo/RTE.hs:13:1: error:
      Failed to load interface for ‘Numeric.IEEE’
      Use -v to see a list of the files searched for.

This is because packages are sandboxed in ``$HOME/.cabal/store``
and you have to explicitly register required packaged in a `GHC environment
<https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/packages.html#package-environments>`_.
This can be done by running the following command:

.. code-block:: bash

  cabal v2-install --lib Agda ieee754

This will register `ieee754
<http://hackage.haskell.org/package/ieee754>`_ in the GHC default environment.

You may want to keep the default environment clean, e.g. to avoid conflicts with
other installed packages. In this case you can a create separate Agda
environment by running:

.. code-block:: bash

  cabal v2-install --package-env agda --lib Agda ieee754

You then have to set the ``GHC_ENVIRONMENT`` when you invoke Agda:

.. code-block:: bash

    GHC_ENVIRONMENT=agda agda -c hello-world.agda

.. NOTE::

  Actually it is not necessary to register the Agda library,
  but doing so forces Cabal to install the same version of `ieee754
  <http://hackage.haskell.org/package/ieee754>`_ as used by Agda.

.. Warning::
  If you are installing Agda using Cabal on Windows, depending on your
  system locale setting, ``cabal install Agda`` may fail with an error
  message:

  .. code-block:: bash

      hGetContents: invalid argument (invalid byte sequence)

  If this happens, you can try changing the `console code page <https://docs.microsoft.com/en-us/windows-server/administration/windows-commands/chcp>`_
  to UTF-8 using the command:

  .. code-block:: bash

    CHCP 65001

Using ``stack``
^^^^^^^^^^^^^^^

For installing the ``agda`` and the ``agda-mode`` programs using
``stack`` run the following commands:

.. code-block:: bash

  cabal get Agda-X.Y.Z
  cd Agda-X.Y.Z
  stack --stack-yaml stack-x.y.z.yaml install

replacing `X.Y.Z` by the Agda version on Hackage
and `x.y.z` by your GHC version, respectively.

Step 3 : Running the ``agda-mode`` program
------------------------------------------
**Warning**: Installing ``agda-mode`` via ``melpa`` is discouraged.
It is strongly advised to install ``agda-mode`` for ``emacs`` as described below:

After installing the ``agda-mode`` program using ``cabal`` or
``stack`` run the following command:

.. code-block:: bash

  agda-mode setup

The above command tries to set up Emacs for use with Agda via the
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

Step 4 : Installing the standard library
----------------------------------------

Installing the standard library, should you choose to use it,
is an additional step using `a separate repository <https://github.com/agda/agda-stdlib/blob/master/notes/installation-guide.md>`_.


.. _prebuilt-packages:

Prebuilt Packages and System-Specific Instructions
==================================================

**Warning** : Depending on the system, prebuild packages may not be
the last release. See https://repology.org/project/agda/versions.

Arch Linux
----------

The following prebuilt packages are available:

* `Agda <https://www.archlinux.org/packages/community/x86_64/agda/>`_

* `Agda standard library <https://www.archlinux.org/packages/community/x86_64/agda-stdlib/>`_

However, due to significant packaging bugs such as `this <https://bugs.archlinux.org/task/61904?project=5&string=agda>`_, you might want to use alternative installation methods.

Debian / Ubuntu
---------------

Prebuilt packages are available for Debian and Ubuntu from Karmic onwards. To install:

.. code-block:: bash

  apt-get install agda agda-mode

This should install Agda and the Emacs mode.

The standard library is available in Debian and Ubuntu from Lucid onwards. To install:

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


Nix or NixOS
------------

Agda is part of the Nixpkgs collection that is used by
https://nixos.org/nixos. There are two ways to install Agda from nix:

* The new way: If you are tracking ``nixos-unstable`` or
  ``nixpkgs-unstable`` (the default on MacOS) or you are using NixOS
  version 20.09 or above then you should be able to install Agda (and
  the standard library) via:

  .. code-block:: bash

    nix-env -f "<nixpkgs>" -iE "nixpkgs: (nixpkgs {}).agda.withPackages (p: [ p.standard-library ])"
    agda-mode setup
    echo "standard-library" > ~/.agda/defaults

  The second command tries to set up the Agda emacs mode. Skip this if
  you don't want to set up the emacs mode. See `Installation from
  source`_ above for more details about ``agda-mode setup``. The
  third command sets the ``standard-library`` as a default library so
  it is always available to Agda. If you don't want to do this you can
  omit this step and control library imports on a per project basis
  using an ``.agda-lib`` file in each project root.

  If you don't want to install the standard library via nix then you
  can just run:

  .. code-block:: bash

    nix-env -f "<nixpkgs>" -iA agda
    agda-mode setup


  For more information on the Agda infrastructure in nix, and how to
  manage and develop Agda libraries with nix, see
  https://nixos.org/manual/nixpkgs/unstable/#agda. In particular, the
  ``agda.withPackages`` function can install more libraries than just
  the standard library. Alternatively, see :ref:`Library Management
  <package-system>` for how to manage libraries manually.

* The old way (deprecated): As Agda is a Haskell package available
  from Hackage you can install it like any other Haskell package:

  .. code-block:: bash

    nix-env -f "<nixpkgs>" -iA haskellPackages.Agda
    agda-mode setup

  This approach does not provide any additional support for working
  with Agda libraries. See :ref:`Library Management <package-system>`
  for how to manage libraries manually. It also suffers from this
  `open issue <https://github.com/agda/agda/issues/4613>`_ which the 'new
  way' does not.

Nix is extremely flexible and we have only described how to install
Agda globally using ``nix-env``. One can also declare which packages
to install globally in a configuration file or pull in Agda and some
relevant libraries for a particular project using ``nix-shell``.

The Agda git repository is a `Nix flake <https://nixos.wiki/wiki/Flakes>`_
to allow using a development version with Nix. The flake has the following
outputs:

- ``overlay``: A ``nixpkgs`` `overlay <https://nixos.wiki/wiki/Overlays>`_
  which makes ``haskellPackages.Agda`` (which the top-level ``agda``
  package depends on) be the build of the relevant checkout.
- ``haskellOverlay``: An overlay for ``haskellPackages`` which overrides
  the ``Agda`` attribute to point to the build of the relevant checkout.
  This can be used to make the development version available at a different
  attribute name, or to override Agda for an alternative haskell package
  set.

OS X
----

`Homebrew <https://brew.sh>`_ is a free and open-source software package
management system that provides prebuilt packages for OS X. Once it is
installed in your system, you are ready to install agda. Open the
Terminal app and run the following commands:

.. code-block:: bash

  brew install agda
  agda-mode setup

This process should take less than a minute, and it installs Agda together with
its Emacs mode and its standard library. For more information about the ``brew``
command, please refer to the `Homebrew documentation <https://docs.brew.sh/>`_
and `Homebrew FAQ <https://docs.brew.sh/FAQ>`_.

By default, the standard library is installed in the folder
``/usr/local/lib/agda/``.  To use the standard library, it is
convenient to add the location of the agda-lib file ``/usr/local/lib/agda/standard-library.agda-lib``
to the ``~/.agda/libraries`` file, and write the line ``standard-library`` in
the ``~/.agda/defaults`` file. To do this, run the following commands:

.. code-block:: bash

  mkdir -p ~/.agda
  echo $(brew --prefix)/lib/agda/standard-library.agda-lib >>~/.agda/libraries
  echo standard-library >>~/.agda/defaults

Please note that this configuration is not performed automatically. You can
learn more about :ref:`using the standard library <use-std-lib>` or
:ref:`using a library in general <use-lib>`.

It is also possible to install with the command-line option keyword ``--HEAD``.
This requires building Agda from source.

To configure the way of editing agda files, follow the section
:ref:`Emacs mode <emacs-mode>`.

.. NOTE::

   If Emacs cannot find the ``agda-mode`` executable, it might help to
   install the exec-path-from-shell_ package by doing ``M-x
   package-install RET exec-path-from-shell RET`` and adding the line
   ``(exec-path-from-shell-initialize)`` to your ``.emacs`` file.

Windows
-------

A precompiled version of Agda 2.6.0.1 bundled with Emacs 26.1 with the
necessary mathematical fonts, is available at
http://www.cs.uiowa.edu/~astump/agda.

.. _installation-development-version:

Installation of the Development Version
=======================================

After getting the development version from the Git `repository
<https://github.com/agda/agda>`_

* Install the :ref:`prerequisites <prerequisites>`.
  Note that for the development version
  :option:`enable-cluster-counting` is on by default,
  so unless you manage to turn it off, you also need to
  install the :ref:`ICU library <icu-install>`.

* In the top-level directory of the Agda source tree, run:

  .. code-block:: bash

    cabal update
    make install

  To install via ``stack`` instead of ``cabal``, copy one of the
  ``stack-x.y.z.yaml`` files of your choice to a ``stack.yaml`` file before
  running ``make``. For example:

  .. code-block:: bash

    cp stack-8.10.7.yaml stack.yaml
    make install

.. _installation-flags:

Installation Flags
==================

When installing Agda the following flags can be used:

.. option:: debug

     Enable debugging features that may slow Agda down. Default: off.

.. option:: enable-cluster-counting

     Enable the Agda option :option:`--count-clusters`. Note that if
     ``enable-cluster-counting`` is ``False``, then option
     :option:`--count-clusters` triggers an error
     message when given to Agda.
     Default: off.

.. option:: optimise-heavily

     Optimise Agda heavily. (In this case it might make sense to limit
     GHC's memory usage.) Default: off.

.. _exec-path-from-shell: https://github.com/purcell/exec-path-from-shell

.. _installing-multiple-versions-of-Agda:

Installing multiple versions of Agda
====================================

Multiple versions of Agda can be installed concurrently by using the --program-suffix flag.
For example:

.. code-block:: bash

  cabal install Agda-2.6.1 --program-suffix=-2.6.1

will install version 2.6.1 under the name agda-2.6.1. You can then switch to this version
of Agda in Emacs via

.. code-block:: bash

   C-c C-x C-s 2.6.1 RETURN

Switching back to the standard version of Agda is then done by:

.. code-block:: bash

   C-c C-x C-s RETURN
