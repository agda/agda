.. _installation:

************
Installation
************

.. hint:: If you want a sneak peek of Agda without installing it, try the
  `Agda Pad <https://agdapad.quasicoherent.io/>`_.

.. hint:: This documentation is for first-time Agda users.
    More advanced "do it yourself" instructions can be found in the Agda repo's
    `HACKING.md <https://github.com/agda/agda/blob/master/HACKING.md>`_ file.

.. _install-agda:

Step 1: Install Agda
====================

You can get the Agda type-checker in at least 4 ways:

.. _install-agda-prebuilt:

Option 1: From package manager
------------------------------

``agda`` binaries are distributed by various package managers.

Installing binaries can be faster than building from source,
but installation problems might be harder to work around.

Repology.org tracks which versions of Agda are offered by various package managers:

.. raw:: html

  <embed src="https://repology.org/badge/vertical-allrepos/agda.svg?columns=4&exclude_unsupported=1&exclude_sources=modules,site">

As well as the repositories tracked by repology,
an OS-independent binary installation of Agda is provided by the `python installer <https://pypi.org/project/agda/>`_.

.. _prebuilt-agda-from-github:

Option 2: From GitHub releases
------------------------------

Pre-built ``agda`` binaries are available for the following platforms:

* Windows (x86-64)
* Linux (x86-64, statically linked)
* macOS (x86-64)
* macOS (arm64, i.e. Apple M-series)

They can be downloaded from the `Agda GitHub releases <https://github.com/agda/agda/releases/>`_ page (under "Assets").

To install, download the appropriate archive, extract the binary, and place it in a directory listed in your ``PATH`` environment variable.

.. _install-agda-dev:

Option 3: From source
---------------------

If you want to work on the Agda compiler itself, or you want to work with the very
latest version of Agda, then you can compile it from source from the `Github repository
<https://github.com/agda/agda>`_.

Both ``cabal install``-based and ``nix build``-based developer builds are maintained.

Miscellaneous developer information is available in the repository's ``HACKING.md``.

.. _install-agda-from-editor:

Option 4: From text editor
--------------------------

Some text editor extensions (e.g. ``banacorn.agda-mode`` for VSCode) can install Agda on their own.

.. _install-text-editor:

Step 2: Configure a text editor
===============================

Your choice of text editor matters more in Agda than it does in most other programming languages.
This is because Agda code typically uses a lot of unicode symbols, and because you will typically
*interact* with Agda through the text editor while writing your program.

Editors with interactive support for Agda include:

* Emacs (:ref:`agda-mode <emacs-mode>`) (most tested)

* Visual Studio Code (`banacorn.agda-mode
  <https://github.com/banacorn/agda-mode-vscode>`_)

* Neovim (`Cornelis
  <https://github.com/isovector/cornelis>`_)

* Vim (`agda-vim
  <https://github.com/derekelkins/agda-vim>`_)

.. _install-agda-stdlib:

Step 3: Install ``agda-stdlib`` (optional)
==========================================

You may want to install Agda's `standard library <https://github.com/agda/agda-stdlib>`_,
although Agda will work without it.

You can install this like any other Agda library (see :ref:`package-system`).
See the `agda-stdlib project's installation instructions <https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md>`_
for the steps to take to install the latest version.

.. _install-ghc:

Step 4: Install ``ghc`` (optional)
==================================

To compile your Agda code to an executable, ``agda`` calls the Haskell compiler ``ghc``, which is not bundled with most Agda distributions.
You can install ``ghc`` spearately with e.g. `GHCUp <https://www.haskell.org/ghcup/>`_.

No separate programs are called by Agda's :ref:`JavaScript backend <javascript-backend>`.
