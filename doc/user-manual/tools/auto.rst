.. _auto:

*****************************
Automatic Proof Search (Auto)
*****************************

Agda supports (since version 2.2.6) the command ``Auto``, that searches
for type inhabitants and fills a hole when one is found. The type
inhabitant found is not necessarily unique.

Auto can be used as an aid when interactively constructing terms in
Agda. In a system with dependent types it can be meaningful to use
such a tool for finding fragments of, not only proofs, but also
programs. One should not expect it to handle large problems of any particular
kind, but small enough problems of almost any kind.

Any solution coming from Auto is checked by Agda. Also, the main
search algorithm has a timeout mechanism. Therefore, there is little
harm in trying Auto and it might save you key presses.

Auto was completely rewritten for Agda version 2.7.0.

Usage
=====

The tool is invoked by placing the cursor on a hole and choosing
``Auto`` in the goal menu or pressing ``C-c C-a``. Auto's behaviour
can be changed by using various options which are passed directly
in the hole.


=======================  =========================================================
Option                   Meaning
=======================  =========================================================
:samp:`-t {N}`           Set timeout to :samp:`{N}` seconds

:samp:`{ID}`             Use definition :samp:`{ID}` as a hint

:samp:`-m`               Use the definitions in the current module as hints

:samp:`-u`               Use the unqualified definitions in scope as hints

:samp:`-l`               List up to ten solutions, does not commit to any

:samp:`-s {N}`           Skip the :samp:`{N}` first solutions
=======================  =========================================================

Giving no arguments is fine and results in a search with
default parameters. The search carries on until either a (not
necessarily unique) solution is found, the search space is fully (and
unsuccessfully) explored or it times out (one second by
default). Here follows a list of the different modes and parameters.

Hints
-----

Auto does not by default try using constants in scope. If there is a
lemma around that might help in constructing the term you can include
it in the search by giving hints. There are two ways of doing
this. One way is to provide the exact list of constants to
include. Such a list is given by writing a number of constant names
separated by space: ``<hint1> <hint2> ...``.

You can also use ``-m`` to use all constants defined in the innermost module
containing the current hole, or ``-u`` to use all constants that are in scope
unqualified. Both options can be combined with an explicit list of named
constants.

There are a few exceptions to what you have to specify as hints:

* Datatypes and constants that can be deduced by unifying the two
  sides of an equality constraint can be omitted.

  E.g., if the constraint ``? = List A`` occurs during the search,
  then refining ``?`` to ``List ...`` will happen without having to
  provide ``List`` as a hint. The constants that you can leave out
  overlap more or less with the ones appearing in hidden arguments,
  i.e. you wouldn’t have written them when giving the term by hand
  either.

* Constructors and projection functions are automatically tried, so
  should never be given as hints.

* Recursive calls, although currently only the function itself, not
  all functions in the same mutual block.

Timeout
-------

The timeout is one second by default but can be changed by adding
``-t <n>`` to the parameters, where ``<n>`` is the number of seconds.

Listing and choosing among several solutions
--------------------------------------------

Normally, Auto replaces the hole with the first solution found. If you
are not happy with that particular solution, you can list the ten (at
most) first solutions encountered by including the flag ``-l``.

You can then pick a particular solution by writing ``-s <n>`` where
``<n>`` is the number of solutions to skip (as well as the number
appearing before the solution in the list). The options ``-l`` and
``-s <n>`` can be combined to list solutions other than the ten first
ones.

Dependencies between meta variables
-----------------------------------

The following feature is `missing <https://github.com/agda/agda/issues/7110>`_
from Agda 2.7.0's implementation of Auto:
*If the goal type or type of local variables contain meta variables,
then the constraints for these are also included in the search. If a
solution is found it means that Auto has also found solutions for the
occurring meta variables. Those solutions will be inserted into your
file along with that of the hole from where you called Auto. Also, any
unsolved equality constraints that contain any of the involved meta
variables are respected in the search.*

Limitations
===========

* Literals other than natural numbers are not supported.

User feedback
==============

When sending bug reports, please use Agda’s `bug tracker
<https://github.com/agda/agda/issues>`_. Apart from that, receiving
nice examples (via the bug tracker) would be much appreciated. Both
such examples which Auto does not solve, but you have a feeling it’s
not larger than for that to be possible. And examples that Auto only
solves by increasing timeout. The examples sent in will be used for
tuning the heuristics and hopefully improving the performance.
