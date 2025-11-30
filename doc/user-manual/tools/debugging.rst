.. _debugging:

*********************
Debugging
*********************

.. warning:: The following page contains information that is mostly of interest to
  developers of Agda, or those who would like to get a deeper understanding of the
  implementation of Agda.

Verbose mode
------------

If Agda was installed with the :option:`debug` flag (e.g. using ``cabal install
Agda -fdebug``), it can print internal information by setting the
:option:`--verbose={N}` flag (or :option:`-v {N}`) with a verbosity tag and a
verbosity level in form ``tag:level``. For example, running Agda with
``--verbose=tc.term:30`` turns on debug printing for the verbosity key
``tc.term`` at verbosity level ``30``. Verbosity levels range between 0 and 100.

* Activating a verbosity key will also enable all the verbosity keys that
  are nested under it, for example ``-v tc:30`` will also print debugging
  information with key ``tc.term``.

* The higher the verbosity level, the more
  detailed debugging information will be printed, for example ``-v tc.term:50``
  will include debugging information at verbosity level 30.
  
By convention, very gory details will be printed only with verbosity of at least 50, so it is advisable in most cases to keep the level below 50.


Verbosity tags and levels can be found by inspecting the source code of Agda by
searching for calls to ``reportSLn`` and ``reportSDoc``. Below are a few common
debug flags that might be useful for developers:

* ``import``: import statements
* ``interaction``: interactive commands

   - ``interaction.case``: case splitting
   - ``interaction.eval``
   - ``interaction.give``
   - ``interaction.helper``
   - ``interaction.intro``
   - ``interaction.refine``
* ``mimer``: automatic proof search
* ``rewriting``: rewrite rules
* ``scope``: scope checking
* ``tc``: type checking

   - ``tc.abstract``: abstract definitions
   - ``tc.cc``: compiling clauses to a case tree
   - ``tc.conv``: conversion checking
   - ``tc.constr``: constraint solving
   - ``tc.cover``: coverage checking
   - ``tc.data``: data types
   - ``tc.def``: function definitions
   - ``tc.generalize``: variable generalization
   - ``tc.instance``: instance arguments
   - ``tc.irr``: irrelevance
   - ``tc.lhs``: left-hand sides of function clauses
   - ``tc.meta``: metavariables
   - ``tc.mod``: modules and module parameters
   - ``tc.term``: type checking of terms
   - ``tc.opaque``: opaque definitions
   - ``tc.pos``: positivity analysis
   - ``tc.reduce``: evaluation of terms and types
   - ``tc.size``: sized types
   - ``tc.sort``: checking sorts
   - ``tc.with``: with abstraction
* ``term``: termination checking
* ``warning``: warnings
