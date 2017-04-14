.. _auto:

*****************************
Automatic Proof Search (Auto)
*****************************

Agda supports (since version 2.2.6) command ``Auto``, that searches
for type inhabitants and fills a hole when one is found. The type
inhabitant found is not necessarily unique.

Auto can be used as an aid when interactively constructing terms in
Agda. In a system with dependent types it can be meaningful to use
such a tool for finding fragments of, not only proofs, but also
programs. For instance, giving the type signature of the map function
over vectors, you will get the desired function as the first solution.

The tool is based on a term search implementation independent of Agda
called Agsy. Agsy is a general purpose search algorithm for a
dependently typed language similar to Agda. One should not expect it
to handle large problems of any particular kind, but small enough
problems of almost any kind.

Any solution coming from Auto is checked by Agda. Also, the main
search algorithm has a timeout mechanism. Therefore, there is little
harm in trying Auto and it might save you key presses.

Usage
=====

The tool is invoked by placing the cursor on a hole and choosing
``Auto`` in the goal menu or pressing ``C-c C-a``.

Search parameters are given by entering them into the hole before
invocation. Giving no arguments is fine and results in a search with
default parameters. The search carries on until either a (not
necessarily unique) solution is found, the search space is fully (and
unsuccessfully) explored or it times out (five seconds by
default). Here follows a list of the different modes and parameters.

Case split
----------

Auto normally only tries to find a term that could replace the current
hole. However, if the hole constitutes the entire RHS of the clause
(same as for the make-case command), you can instruct Auto to try case
splitting by writing (since version 2.2.8) ``-c``.

Note that if a solution is found the whole file will be reloaded (as
for make-case) resulting in a delay. Case splitting cannot yet be
combined with ``-l`` or ``-s <n>``.

Equality reasoning
------------------

If the constants ``_≡_ begin_ _≡⟨_⟩_ _∎ sym cong`` from the standard
library are in scope, then Auto will do equality reasoning using these
constructs. However, it will not do anything more clever than things
like not nesting several ``sym`` or ``cong``. Hence long chains of
equalities should not be expected and required arithmetical rules have
to be given as hints.

Hints
-----

Auto does not by default try using constants in scope. If there is a
lemma around that might help in constructing the term you can include
it in the search by giving hints. There are two ways of doing
this. One way is to provide the exact list of constants to
include. Such a list is given by writing a number of constant names
separated by space: ``<hint1> <hint2> ...``.

The other way is to write ``-m``. This includes all constants in scope
which are defined or postulated in the innermost module surrounding
the current hole. It is also possible to combine ``-m`` with a list of
named constants (not included by ``-m``).

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

The timeout is five seconds by default but can be changed by adding
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

Disproving
----------

If you are uncertain about the validity of what you are trying to
prove, you can use Auto to try to find a counterproof. The flag ``-d``
makes Auto negate the current goal and search for a term disproving
it. If such a term is found, it will be displayed in the info
buffer. The flag ``-d`` can be combined with ``-l`` and ``-l -s <n>``.

Auto refine / suggest
---------------------

There is a special mode for searching (part of) the scope of constants
for possible refinement candidates. The flag ``-r`` chooses this
mode. By default all constants which are in scope unqualified are
included. By adding ``-a`` all constants in scope are included, but
this often takes too long when importing things from the standard
library. However, it might be possible to implement this mode more
efficiently.

The constants that matches the current goal are sorted in order of how
many constructs their result type contains. This means that the
constants which in some sense match the goal most specifically will
appear first and the most general ones last. By default, Auto will
present a list of candidates, rather than refining using the topmost
constant. To select one of them for refinement, combine ``-r`` with
``-s <n>``. In order to list constants other than the ten first ones,
write ``-r -l -s <n>``.

The auto refine feature has little to do with the rest of the Auto
tool. If it turns out to be useful it could be improved and made into
a separate Emacs mode command.

Dependencies between meta variables
-----------------------------------

If the goal type or type of local variables contain meta variables,
then the constraints for these are also included in the search. If a
solution is found it means that Auto has also found solutions for the
occurring meta variables. Those solutions will be inserted into your
file along with that of the hole from where you called Auto. Also, any
unsolved equality constraints that contain any of the involved meta
variables are respected in the search.

Limitations
===========
* Irrelevance is not yet respected. Agsy will happily use a parameter
  marked as irrelevant and does not disregard irrelevant arguments
  when comparing terms.

* Records that lack a constructor name are still deconstructed when
  case splitting, but the name of the record type is used instead of a
  constructor name in the resulting pattern.

* Literals representing natural numbers are supported (but any
  generated natural number will be given in constructor form). Apart
  from this, literals are not supported.

* Primitive functions are not supported.

* Termination checking for recursive calls is done locally, so a
  non-terminating set of clauses might be sent back to Agda.

* Agsy currently does not automatically pick a datatype when
  instantiating types. A frequently occurring situation is when you
  try to disprove a generic property. Then Agsy must come up with a
  particular type as part of the disproof. You can either fix your
  generic type to e.g. ``Nat`` or ``Fin n`` (for an arbitrary ``n`` if
  you wish), or you give ``Nat`` or ``Fin`` as a hint to the search.

* Case split mode currently does not do case on expressions
  (``with``).

* Case split mode sometimes gives a unnecessarily complex RHS for some
  clause when the solution consists of several clauses.

* The special constraints that apply to ``codata`` are not respected
  by Agsy. Agsy treats ``codata`` just like ``data``.

* Agsy has universe subtyping, so sometimes suggests solutions not
  accepted by Agda.

* Universe polymorphism is only partially supported. Agsy may fail
  when trying to construct universe polymorphic definitions, but will
  probably succeed (with respect to this) when constructing terms
  which refer to, or whose type is defined in terms of, universe
  polymorphic definitions.

* In case split and disproving modes, the current goal may not depend
  on any other meta variables. For disproving mode this means that
  there may be implicitly universally quantified but not existentially
  quantified stuff.

* Searching for simultaneous solutions of several holes does not
  combine well with parameterised modules and recursive calls.

User feedback
==============

When sending bug reports, please use Agda’s `bug tracker
<https://github.com/agda/agda/issues>`_. Apart from that, receiving
nice examples (via the bug tracker) would be much appreciated. Both
such examples which Auto does not solve, but you have a feeling it’s
not larger than for that to be possible. And examples that Auto only
solves by increasing timeout. The examples sent in will be used for
tuning the heuristics and hopefully improving the performance.
