.. _installation:

************
Installation
************

To get started with Agda, follow these three steps:

* :ref:`install-agda`
* :ref:`install-agda-stdlib`
* :ref:`install-text-editor`

In case of installation problems, check the section on :ref:`troubleshooting <troubleshooting>`.

.. hint:: If you want a sneak peek of Agda without installing it, try the
  `Agda Pad <agda-pad_>`_.

.. _agda-pad: https://agdapad.quasicoherent.io/

.. _install-agda:

Step 1: Install Agda
====================

There are at least three options for installing Agda:

.. _install-agda-cabal:

Option 1: Install Agda as a Haskell Package (recommended)
---------------------------------------------------------

Agda is intimately connected to the Haskell programming language: it is written
in Haskell and its :ref:`GHC Backend <ghc-backend>` translates
Agda programs into Haskell programs.
So the most common way to install Agda and keep it up to date is through Haskell's
package manager, Cabal.

.. _zlib-ncurses:

``zlib`` and ``ncurses`` Dependency
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Non-Windows users need to ensure that the development files for the C
libraries *zlib* and *ncurses* are installed (see https://zlib.net
and https://www.gnu.org/software/ncurses/). Your package manager may be
able to install these files for you. For instance, on Debian or Ubuntu
it should suffice to run

.. code-block:: bash

  apt-get install zlib1g-dev libncurses5-dev

as root to get the correct files installed.

Install GHC and Cabal through GHCup
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Follow the `GHCup installation instructions <https://www.haskell.org/ghcup/>`_
to install GHC and Cabal (see :ref:`ghc-versions` for a list of supported GHC
versions). You should now have the ``ghc`` and ``cabal`` commands available.

Use ``cabal`` to install Agda
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Now that you have ``cabal`` installed, use it to install Agda as a Haskell package:

.. code-block:: bash

  cabal update
  cabal install Agda

You should now have the ``agda`` and ``agda-mode`` commands available.

.. hint:: If these commands aren't available, check that programs installed by ``cabal``
  are on your shell's search path. This should have been done during the installation
  of ``cabal``, but if not, the installation location is described by field ``installdir``
  in the cabal configuration (check ``~/.cabal/config``; it defaults to ``~/.cabal/bin``).
  So e.g. under Ubuntu or MacOS you may need to add ``export PATH=~/.cabal/bin:$PATH``
  to your ``.profile`` or ``.bash_profile``.

.. note:: Some installation options are available through :ref:`installation-flags`,
  although in most cases the defaults should be fine.

.. _install-agda-dev:

Option 2: Install the Development Version of Agda from Source (for advanced users)
----------------------------------------------------------------------------------

If you want to work on the Agda compiler itself, or you want to work with the very
latest version of Agda, then you can compile it from source from the `Github repository
<https://github.com/agda/agda>`_.

You should have GHC and Cabal installed (if not see the instructions in :ref:`install-agda-cabal`).

.. note:: For the development version :option:`enable-cluster-counting` is on by default,
  so unless you turn it off (see :ref:`installation-flags`, below), you also need to
  install the :ref:`ICU library <icu-install>`.

Install ``alex`` and ``happy`` dependencies
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Agda depends on the ``alex`` and ``happy`` tools, but depending on your system
and version of Cabal these might not be installed automatically. You can use
Cabal to install them manually:

.. code-block:: bash

  cabal update
  cabal install alex happy

Build Agda using Cabal
^^^^^^^^^^^^^^^^^^^^^^

In the top-level directory of the Agda source tree, run:

  .. code-block:: bash

    cabal update
    make install

Build Agda using Stack
^^^^^^^^^^^^^^^^^^^^^^

To install via ``stack`` instead of ``cabal``, copy one of the
``stack-x.y.z.yaml`` files of your choice to a ``stack.yaml`` file before
running ``make``. For example:

  .. code-block:: bash

    cp stack-8.10.7.yaml stack.yaml
    make install


.. _install-agda-prebuilt:

Option 3: Install Agda as a Prebuilt Package
--------------------------------------------

Packaged Agda binaries and the Agda standard library are provided by various package managers.
Installing Agda binaries can be faster than installing Agda from source,
but installation problems might be harder to work around.

An OS-independent binary installation of Agda is provided by the :ref:`python installer <pip-install>`.

.. Warning::
  Depending on the system, prebuilt packages may not contain the latest release of Agda.
  See `repology <https://repology.org/project/agda/versions>`_
  for a list of Agda versions available on various package managers.

See :ref:`prebuilt-packages` for a list of known systems and their system-specific instructions.


.. _install-agda-stdlib:

Step 2: Install the Agda Standard Library (agda-stdlib)
=======================================================

Most users will want to install the `standard library <https://github.com/agda/agda-stdlib>`_.
You can install this as any other Agda library (see :ref:`package-system`).
See the `agda-stdlib project's installation instructions <https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md>`_
for the steps to take to install the latest version.


.. _install-text-editor:

Step 3: Install and Configure a Text Editor for Agda
====================================================

Your choice of text editor matters more in Agda than it does in most other programming languages.
This is because Agda code typically uses a lot of unicode symbols, and because you will typically
*interact* with Agda through the text editor while writing your program.

The most common choice is `Emacs <https://www.gnu.org/software/emacs/>`_.
Other editors with interactive support for Agda include

* Visual Studio Code (`agda-mode on VS Code
  <https://github.com/banacorn/agda-mode-vscode>`_)

* Neovim (`Cornelis
  <https://github.com/isovector/cornelis>`_), and

* Vim (`agda-vim
  <https://github.com/derekelkins/agda-vim>`_)

.. _install-agda-mode:

Emacs
-----

Emacs has good support for unicode input, and the ``agda-mode`` for emacs is maintained
by the Agda developers in the main Agda repository and offers many advanced features.

Running the ``agda-mode`` program
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. Warning::
  Installing ``agda-mode`` via ``melpa`` is discouraged.
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

.. Warning::
  If you reinstall the Agda mode without recompiling the Emacs Lisp files,
  then Emacs may continue using the old, compiled files.


Installation Reference
======================

.. _troubleshooting:

Troubleshooting
---------------

A Common Issue on Windows: Invalid Byte Sequence
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If you are installing Agda using Cabal on Windows, depending on your
system locale setting, ``cabal install Agda`` may fail with an error
message:

.. code-block:: bash

    hGetContents: invalid argument (invalid byte sequence)

If this happens, you can try changing the `console code page <https://docs.microsoft.com/en-us/windows-server/administration/windows-commands/chcp>`_
to UTF-8 using the command:

.. code-block:: bash

  CHCP 65001


.. _missing-ieee754:

A Common Issue: Missing ieee754 Dependency
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

You may get the following error when compiling with the GHC backend::

  Compilation error:

  MAlonzo/RTE/Float.hs:6:1: error:
      Failed to load interface for ‘Numeric.IEEE’
      Use -v to see a list of the files searched for.

This is because packages are sandboxed in the Cabal store (e.g. ``$HOME/.cabal/store``)
and you have to explicitly register required packages in a `GHC environment
<https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/packages.html#package-environments>`_.
This can be done by running the following command:

.. code-block:: bash

  cabal install --lib Agda ieee754

This will register `ieee754 <https://hackage.haskell.org/package/ieee754>`_
in the GHC default environment.

Cabal install fails due to dynamic linking issues
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If you have setting ``executable-dynamic: True`` in your cabal configuration
then installation might fail on Linux and Windows.

Cure: change to default ``executable-dynamic: False``.

Further information:

  * https://github.com/agda/agda/issues/7163
  * https://github.com/haskell/cabal/issues/9784


Agda and Haskell
----------------

.. _ghc-versions:

Tested GHC Versions
^^^^^^^^^^^^^^^^^^^

Agda has been tested with GHC
8.8.4,
8.10.7,
9.0.2,
9.2.8,
9.4.8,
9.6.6,
9.8.2 and
9.10.1.


.. _installation-flags:

Installation Flags
^^^^^^^^^^^^^^^^^^

When installing Agda the following flags can be used:

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

.. option:: enable-cluster-counting

     Enable :ref:`cluster counting <grapheme-clusters>`.
     This will require the `text-icu Haskell library <https://hackage.haskell.org/package/text-icu>`_,
     which in turn requires that :ref:`ICU be installed <icu-install>`.
     Note that if ``enable-cluster-counting`` is ``False``, then option
     :option:`--count-clusters` triggers an error message when given to Agda.
     Default: off, but on for development version.

.. option:: optimise-heavily

     Optimise Agda heavily. (In this case it might make sense to limit
     GHC's memory usage.) Default: off.

.. hint:: During ``cabal install`` you can add build flags using the ``-f`` argument:
    ``cabal install -fenable-cluster-counting``. Whereas stack uses ``--flag`` and an
    ``Agda:`` prefix, like this: ``stack install --flag Agda:enable-cluster-counting``.

.. _icu-install:

Installing ICU
^^^^^^^^^^^^^^

If cluster counting is enabled (see the ``enable-cluster-counting`` flag above, enabled
by default), then you will need the `ICU <http://site.icu-project.org>`_ library
to be installed. See the `text-icu Prerequisites documentation <https://github.com/haskell/text-icu#prerequisites>`_ for how to install ICU on your system.

Keeping the Default Environment Clean
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

You may want to keep the default environment clean, e.g. to avoid conflicts with
other installed packages. In this case you can a create separate Agda
environment by running:

.. code-block:: bash

  cabal install --package-env agda --lib Agda ieee754

You then have to set the ``GHC_ENVIRONMENT`` when you invoke Agda:

.. code-block:: bash

    GHC_ENVIRONMENT=agda agda -c hello-world.agda

.. NOTE::

  Actually it is not necessary to register the Agda library,
  but doing so forces Cabal to install the same version of
  `ieee754 <https://hackage.haskell.org/package/ieee754>`_
  as used by Agda.

.. _installing-multiple-versions-of-Agda:

Installing Multiple Versions of Agda
------------------------------------

Multiple versions of Agda can be installed concurrently by using the ``--program-suffix`` flag.
For example:

.. code-block:: bash

  cabal install Agda-2.6.4.3 --program-suffix=-2.6.4.3

will install version 2.6.4.3 under the name agda-2.6.4.3. You can then switch to this version
of Agda in Emacs via

.. code-block:: bash

   C-c C-x C-s 2.6.4.3 RETURN

Switching back to the standard version of Agda is then done by:

.. code-block:: bash

   C-c C-x C-s RETURN

.. _prebuilt-packages:

Prebuilt Packages and System-Specific Instructions
--------------------------------------------------

The recommended way to install Agda is :ref:`through cabal <install-agda-cabal>`,
but in some cases you may want to use your system's package manager instead:

Arch Linux
^^^^^^^^^^

The following prebuilt packages are available:

* `Agda <https://www.archlinux.org/packages/extra/x86_64/agda/>`_

* `Agda standard library <https://www.archlinux.org/packages/extra/x86_64/agda-stdlib/>`_

In case of installation problems, please consult the
`issue tracker <https://gitlab.archlinux.org/archlinux/packaging/packages/agda/-/issues>_`.

Debian / Ubuntu
^^^^^^^^^^^^^^^

Prebuilt packages are available for Debian and Ubuntu from Karmic onwards. To install:

.. code-block:: bash

  apt install agda

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

Fedora / EPEL (Centos)
^^^^^^^^^^^^^^^^^^^^^^

Agda is `packaged <https://src.fedoraproject.org/rpms/Agda>`_ for Fedora Linux and EPEL.
Agda-stdlib is `available <https://src.fedoraproject.org/rpms/Agda-stdlib/>`_ for Fedora.

.. code-block:: bash

  dnf install Agda Agda-stdlib

will install Agda with the emacs mode and also agda-stdlib.

FreeBSD
^^^^^^^

Packages are available from `FreshPorts <https://www.freebsd.org/cgi/ports.cgi?query=agda>`_
for Agda and Agda standard library.

GNU Guix
^^^^^^^^

GNU Guix provides packages for both
`agda <https://packages.guix.gnu.org/packages/agda/>`__ and
`agda-stdlib <https://packages.guix.gnu.org/packages/agda-stdlib/>`__.
You can install the latest versions by running:

.. code-block:: bash

  guix install agda agda-stdlib

You can also install a specific version by running:

.. code-block:: bash

  guix install agda@ver agda-stdlib@ver

where ``ver`` is a specific version number.

Packages Sources:

* `Agda <https://git.savannah.gnu.org/cgit/guix.git/tree/gnu/packages/agda.scm#n45>`__

* `Agda-Stdlib <https://git.savannah.gnu.org/cgit/guix.git/tree/gnu/packages/agda.scm#n200>`__


Nix or NixOS
^^^^^^^^^^^^

Agda is part of the Nixpkgs collection that is used by
https://nixos.org/nixos. Install Agda (and the standard library) via:

  .. code-block:: bash

    nix-env -f "<nixpkgs>" -iE "nixpkgs: (nixpkgs {}).agda.withPackages (p: [ p.standard-library ])"
    agda-mode setup
    echo "standard-library" > ~/.agda/defaults

  The second command tries to set up the Agda emacs mode. Skip this if
  you don't want to set up the emacs mode. See :ref:`Installation from
  source <install-agda-dev>` above for more details about ``agda-mode setup``. The
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

Nix is extremely flexible and we have only described how to install
Agda globally using ``nix-env``. One can also declare which packages
to install globally in a configuration file or pull in Agda and some
relevant libraries for a particular project using ``nix-shell``.

The Agda git repository is a `Nix flake <https://wiki.nixos.org/wiki/Flakes>`_
to allow using a development version with Nix. The flake has the following
outputs:

- ``overlay``: A ``nixpkgs`` `overlay <https://wiki.nixos.org/wiki/Overlays>`_
  which makes ``haskellPackages.Agda`` (which the top-level ``agda``
  package depends on) be the build of the relevant checkout.
- ``haskellOverlay``: An overlay for ``haskellPackages`` which overrides
  the ``Agda`` attribute to point to the build of the relevant checkout.
  This can be used to make the development version available at a different
  attribute name, or to override Agda for an alternative haskell package
  set.

OS X
^^^^

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
  echo $(brew --prefix)/lib/agda/standard-library.agda-lib >> ~/.agda/libraries
  echo standard-library >> ~/.agda/defaults

Please note that this configuration is not performed automatically. You can
learn more about :ref:`using the standard library <use-std-lib>` or
:ref:`using a library in general <use-lib>`.

It is also possible to install with the command-line option keyword ``--HEAD``.
This requires building Agda from source.

To configure the way of editing agda files, follow the section
:ref:`Emacs mode <emacs-mode>`.

.. NOTE::

   If Emacs cannot find the ``agda-mode`` executable, it might help to
   install the `exec-path-from-shell <https://github.com/purcell/exec-path-from-shell>`_
   package by doing ``M-x package-install RET exec-path-from-shell RET`` and adding
   the line ``(exec-path-from-shell-initialize)`` to your ``.emacs`` file.

.. _pip-install:

Python Installer (``pip``)
^^^^^^^^^^^^^^^^^^^^^^^^^^

An OS-independent binary install of Agda is provided via the Python Installer:

.. code-block:: bash

  pip install agda

Further information: https://pypi.org/project/agda/

Windows
^^^^^^^

Some precompiled version of Agda bundled with Emacs and the
necessary mathematical fonts, is available at
http://www.cs.uiowa.edu/~astump/agda.

  * Agda 2.6.0.1 bundled with Emacs 26.1
  * Agda 2.6.2.2 ...

.. Warning:: These are old versions of Agda.  It would be much better to use the
  :ref:`Agda as installed by cabal <install-agda-cabal>` instead.
