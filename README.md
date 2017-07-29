Agda 2
======

[![Hackage version](https://img.shields.io/hackage/v/Agda.svg?label=Hackage)](http://hackage.haskell.org/package/Agda)
[![Stackage version](https://www.stackage.org/package/Agda/badge/lts?label=Stackage)](https://www.stackage.org/package/Agda)
[![Build Status](https://travis-ci.org/agda/agda.svg?branch=stable-2.5)](https://travis-ci.org/agda/agda)
[![Documentation Status](https://readthedocs.org/projects/agda/badge/?version=stable-2.5)](http://agda.readthedocs.io/en/stable-2.5/?badge=stable-2.5)

Table of contents:

* [Documentation](#documentation)
* [Prerequisites](#prerequisites)
* [Installing Agda](#installing-agda)
* [Configuring the Emacs mode](#configuring-the-emacs-mode)
* [Installing Emacs under Windows](#installing-emacs-under-windows)

Note that this README only discusses installation of Agda, not its standard
library. See the [Agda Wiki][agdawiki] for information about the library.

Documentation
-------------

* [User manual](http://agda.readthedocs.io)
* [CHANGELOG](https://github.com/agda/agda/blob/master/CHANGELOG.md)

Prerequisites
-------------

You need recent versions of the following programs:

* GHC:           http://www.haskell.org/ghc/
* cabal-install: http://www.haskell.org/cabal/
* Alex:          http://www.haskell.org/alex/
* Happy:         http://www.haskell.org/happy/
* cpphs:         http://projects.haskell.org/cpphs/
* GNU Emacs:     http://www.gnu.org/software/emacs/

You should also make sure that programs installed by cabal-install are
on your shell's search path.

For instructions on installing a suitable version of Emacs under
Windows, see [below](#installing-emacs-under-windows).

Non-Windows users need to ensure that the development files for the C
libraries zlib and ncurses are installed (see http://zlib.net and
http://www.gnu.org/software/ncurses/). Your package manager may be
able to install these files for you. For instance, on Debian or Ubuntu
it should suffice to run

    apt-get install zlib1g-dev libncurses5-dev

as root to get the correct files installed.

Optionally one can also install the [ICU](http://site.icu-project.org)
library, which is used to implement the `--count-clusters` flag. Under
Debian or Ubuntu it may suffice to install `libicu-dev`. Once the ICU
library is installed one can hopefully enable the `--count-clusters`
flag by giving the `-fenable-cluster-counting` flag to `cabal
install`. Note that `make install` by default enables
`-fenable-cluster-counting`.

### Note on GHC's CPP language extension

Recent versions of Clang's preprocessor don't work well with Haskell.
In order to get some dependencies to build, you may need to set up Cabal
to have GHC use cpphs by default. You can do this by adding

    program-default-options
      ghc-options: -pgmPcpphs -optP--cpp

to your .cabal/config file. (You must be using cabal >= 1.18. Note
that some packages may not compile with this option set.)

You don't need to set this option to install *Agda* from the current
development source; Agda.cabal now uses cpphs.


Installing Agda
---------------

There are several ways to install Agda:


### Using a binary package prepared for your platform

Recommended if such a package exists. See the [Agda Wiki][agdawiki].


### Using a released source package from Hackage

Install the prerequisites mentioned above, then run the following commands:

    cabal update
    cabal install Agda
    agda-mode setup

The last command tries to set up Emacs for use with Agda. As an alternative you
can copy the following text to your .emacs file:

    (load-file (let ((coding-system-for-read 'utf-8))
                    (shell-command-to-string "agda-mode locate")))

It is also possible (but not necessary) to compile the Emacs mode's files:

    agda-mode compile

This can, in some cases, give a noticeable speedup.

**WARNING**: If you reinstall the Agda mode without recompiling the Emacs
Lisp files, then Emacs may continue using the old, compiled files.


### Using the development version of the code

You can obtain tarballs of the development version from the [Agda
Wiki][agdawiki], or clone the repository.

Install the prerequisites discussed in [Prerequisites](#prerequisites).

Then, either:

*(1a)* Run the following commands in the top-level directory of the Agda source
tree to install Agda:

    cabal update
    cabal install

*(1b)* Run `agda-mode setup` to set up Emacs for use with Agda. Alternatively,
add the following text to your .emacs file:

    (load-file (let ((coding-system-for-read 'utf-8))
                    (shell-command-to-string "agda-mode locate")))

It is also possible (but not necessary) to compile the Emacs mode's files:

    agda-mode compile

This can, in some cases, give a noticeable speedup.

**WARNING**: If you reinstall the Agda mode without recompiling the Emacs
Lisp files, then Emacs may continue using the old compiled files.

*(2)* Or, you can try to install Agda (including a compiled Emacs mode) by
running the following command:

    make install


Configuring the Emacs mode
--------------------------

If you want to you can customise the Emacs mode. Just start Emacs and
type the following:

    M-x load-library RET agda2-mode RET
    M-x customize-group RET agda2 RET

This is useful if you want to change the Agda search path, in which
case you should change the agda2-include-dirs variable.

If you want some specific settings for the Emacs mode you can add them
to agda2-mode-hook. For instance, if you do not want to use the Agda
input method (for writing various symbols like ∀≥ℕ→π⟦⟧) you can add
the following to your .emacs:

    (add-hook 'agda2-mode-hook
              '(lambda ()
                ; If you do not want to use any input method:
                (deactivate-input-method)
                ; (In some versions of Emacs you should use
                ; inactivate-input-method instead of
                ; deactivate-input-method.)

                ; If you want to use the X input method:
                (set-input-method "X")))

Note that, on some systems, the Emacs mode changes the default font of
the current frame in order to enable many Unicode symbols to be
displayed. This only works if the right fonts are available, though.
If you want to turn off this feature, then you should customise the
agda2-fontset-name variable.

------------------------------------------------------------------------
Installing Emacs under Windows
------------------------------------------------------------------------

A precompiled version of Emacs 24.3, with the necessary mathematical
fonts, is available at http://homepage.cs.uiowa.edu/~astump/agda/

[agdawiki]: http://wiki.portal.chalmers.se/agda/pmwiki.php

Hacking on Agda
---------------

Head to [`HACKING`](https://github.com/agda/agda/blob/master/HACKING)
