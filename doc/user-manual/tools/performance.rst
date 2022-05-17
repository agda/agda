.. _performance:

*********************
Performance debugging
*********************

Sometimes your Agda program doesn't type check or run as fast as you expected. This section
describes some tools available to figure out why not.

.. note::
  This is a stub

Measuring typechecking performance
----------------------------------

Agda can do some internal book-keeping of how time is spent, which can be turned on using the
``--profile`` flag:

.. option:: --profile=definitions

  Break down by time spent checking each top-level definition.

.. option:: --profile=modules

  Break down by time spent checking each top-level module.

.. option:: --profile=internal

  Break down by activity (such as parsing, type checking, termination checking, etc).

The Haskell runtime system can also tell you something about how Agda spends its time:

.. option:: +RTS -s -RTS

  Show memory usage and time spent on garbage collection.

External tools
~~~~~~~~~~~~~~

* `agda-bench <https://github.com/UlfNorell/agda-bench>`_ is a tool for benchmarking compile-time
  evaluation and type checking performance of Agda programs.

Measuring run-time performance
------------------------------

Agda programs are compiled (by default) via Haskell (see :ref:`compilers`), so the GHC profiling
tools can be applied to Agda programs. For instance,

.. code-block:: bash

  > agda -c Test.agda --ghc-flag=-prof --ghc-flag=-fprof-auto
  > ./Test +RTS -p

A complication is that the GHC backend generates names like ``d76``, so making sense of the
profiling output can require a little bit of work.

External tools
~~~~~~~~~~~~~~

* `agda-criterion <https://github.com/UlfNorell/agda-criterion>`_ has bindings for a small part of
  the `criterion <https://hackage.haskell.org/package/criterion>`_ Haskell library for performance
  measurement.

* `agda-ghc-names <https://github.com/agda/agda-ghc-names>`_ can translate the names in generated
  Haskell code back to Agda names.
