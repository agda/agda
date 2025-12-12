
.. _troubleshooting-installation:

****************
Troubleshooting
****************

This section collects tips for fixing common installation errors.
Skip it if Agda installed fine.

This list is not comprehensive,
see `the GitHub issue tracker <https://github.com/agda/agda/issues>`_ for more known bugs.

Windows ``invalid byte sequence``
=================================

If you are installing Agda using Cabal on Windows, depending on your
system locale setting, ``cabal install Agda`` may fail with an error
message:

.. code-block:: bash

    hGetContents: invalid argument (invalid byte sequence)

If this happens, you can try changing the `console code page <https://docs.microsoft.com/en-us/windows-server/administration/windows-commands/chcp>`_
to UTF-8 using the command:

.. code-block:: bash

  CHCP 65001

macOS notarization
==================

``agda`` binaries from :ref:`GitHub releases <prebuilt-agda-from-github>` are not
`notarised by Apple <https://developer.apple.com/documentation/Security/notarizing-macos-software-before-distribution>`_,
so will not run on macOS unless the quarantine attribute is removed, e.g. with ``xattr -c agda``

Cabal issues
============

If you chose to install Agda with a Haskell build tool like ``cabal`` or ``stack``,
see the "Troubleshooting Cabal" section in ``HACKING.md``.
