..
  ::
  module language.type-based-termination-checking where

      open import Agda.Builtin.Nat
      open import Agda.Builtin.List

.. _type-based-termination-checking:

*******************************
Type-Based Termination Checking
*******************************

Sometimes the default termination checker in Agda may seem too weak. Let's explore this in the context of defining a finitely-branching tree:

::

      data RoseTree (A : Set) : Set where
        rose : A → List (RoseTree A) → RoseTree A

      mapRose : {A B : Set} → (A → B) → RoseTree A → RoseTree B
      mapRose f (rose a children) = rose (f a) (map (mapRose f) children)

Intuitively, we observe that ``children`` represents a list of "smaller" rose trees. When we call ``map (mapRose f) children``, we effectively apply ``mapRose f`` to each of these smaller trees. Thus, the function ``mapRose`` terminates, as all recursive calls accept trees smaller than the initial argument of ``mapRose``.

However, ``mapRose`` does not adhere to the pattern of syntactic recursion, as it is passed to another function instead of being directly called on a structurally smaller argument. Agda rejects such definitions because, instead of ``map``, an arbitrary function could be used. This arbitrary function might alter its arguments in unpredictable ways, rendering ``mapRose`` non-terminating.

In our case, we use ``map`` and trust it. The evidence for this trust lies in the type signature of ``map: {A' B' : Set} → (A' → B') → List A' → List B'``. According to this signature, map operates on arbitrary types, meaning it cannot construct a malicious ``RoseTree``. This property, known as parametricity, aligns with the logic of Agda, as described in :ref:`[1]<type-based-termination-checking-references>`.

The idea of the type-based termination checker is that Agda can try to track
the "sizes" of terms, and deduce whether the recursive calls eventually happen on
the terms of smaller sizes. In the case with the rose tree above, we see that ``map``
operates on a type ``A' := RoseTree A``, where the type of arguments of ``mapRose f``
is ``A'``, and the type of elements in ``children`` is also ``A'``. We can conclude
that ``mapRose f``, if ever called, is invoked on the same elements as those in
``children``, hence it makes a recursive call on a smaller argument than the enclosing function was initially called with.

.. _type-based-termination-checking-usage:

Usage
-----

To activate the type-based termination checker in Agda, you can use the option ``--type-based-termination``:

::

      {-# OPTIONS --type-based-termination #-}

      id : {A : Set} → A → A
      id x = x

      plus : Nat → Nat → Nat
      plus zero    m = m
      plus (suc n) m = suc (plus (id n) m) -- note 'id' here

Enabling this option is the only requirement to utilize the type-based termination checker.

It's important to note that the type-based termination checker requires preprocessing of all datatypes involved in the checking process. For the provided definitions, the files containing ``Nat``, ``List``, and ``RoseTree`` should all be type-checked with the ``--type-based-termination`` option enabled.

By default, type-based termination is disabled. You can also explicitly disable it by specifying ``--no-type-based-termination``.

Additionally, there's an option ``--(no-)syntax-based-termination`` that enables or disables the default syntax-based termination checker. This option can be useful if you wish to exclusively experiment with the type-based termination.

Another option is ``--(no-)size-preservation``, explained
:ref:`here<type-based-termination-checking-size-preservation>`.

For a deeper understanding of the internal behavior of the type-based termination checker, you can use the verbosity option ``term.tbt`` with different levels. An example of usage is ``{-# OPTIONS -v term.tbt:40 #-}`` in the file header. This option dumps the output of the checker. Note that Agda needs to be built in debug mode to print any verbose data.


.. _type-based-termination-checking-inductive:

Inductive definitions
---------------------

The core principle of the type-based termination is that it checks the terms of Agda
against its own type system, which is further referred to as *size types*. Size types closely resemble regular types in Agda, but they pivot around size variables.
The process of type-checking against size types is further referred to as
*size checking*.

Let's illustrate this with an example.

Consider the datatype of natural numbers:

::

      data Nat : Set where
        zero : Nat
        suc  : Nat → Nat

This datatype is *encoded* into a size type. We shall represent ``Nat`` as a single
size variable, let's denote it as ``t₀``. Constructor ``zero`` has no
parameters, we shall also represent it as a single size variable ``t₁``. The constructor ``suc``, on the other hand, has a parameter, leading to its encoding as ``t₂ → t₃``, with the additional constraint that ``t₂ < t₃``.


Now, let's examine how a function is processed. Consider the following function, which essentially returns its second argument:

::

      f : Nat → Nat → Nat
      f zero    m = m
      f (suc n) m = f n m

In the case of a function, its type is also encoded, resulting in ``t₄ → t₅ → t₆``. The checker then begins processing the clauses.

The clause ``f zero m = m`` indicates that we have terms ``zero : t₄`` and ``m : t₅``, and we need to size-check ``m`` (the body of the clause) against the size type ``t₆`` (the expected type of the clause). Since this branch lacks recursive calls, these constraints are not particularly useful.

The clause ``f (suc n) m = f n m`` is more intricate. Due to pattern-matching, new size variables are introduced. Here, we work with ``n : t₇`` and ``m : t₅``. Crucially, we know that ``t₇ < t₄`` because of the inequality provided by the ``suc`` constructor. The variables obtained during pattern-matching (here, ``t₄``, ``t₅``, ``t₆``, and ``t₇``) are called *rigid*, and the goal of the type-based checker is to assign all other variables (termed *flexible*) to the rigid ones.

After the pattern-matching, the checking of the body starts. Here we see that a
recursive call is used. During the process of size checking, every usage of a function is *refreshed* with a set of new flexible variables, so
in this particular place we have ``f : t₈ → t₉ → t₁₀``. Now, since we apply ``f`` to
``n``, we learn that we need to respect a constraint ``t₇ ≤ t₈``, and similarly ``t₅ ≤ t₉`` for the call with ``m``. The return type also induces its constraint
``t₁₀ ≤ t₆``. For this particular function, the constraint on return type is not that interesting.

The subsequent step involves assigning flexible variables. For this clause, the flexible variables are ``t₈``, ``t₉``, and ``t₁₀``, and we need to find a rigid assignment for each that respects the earlier constraints. A valid assignment would be ``t₈ := t₇``, ``t₉ := t₅``, and ``t₁₀ := t₆``.

Finally, this information is applied to determine if the function terminates. In this case, we observe a recursive call to ``f`` with sizes ``t₇``, ``t₅``, and ``t₆``, where ``t₇ < t₄``. This indicates that the function is called with a smaller argument, confirming its termination.

The description above provides a simplified overview of the actual process within the type-based termination checker, covering the essential steps of the process.

.. _type-based-termination-checking-coinduction:

Coinductive definitions
-----------------------

The type-based termination checker in Agda extends its default guardedness checker to support coinductive definitions. The fundamental idea behind coinductive type-based termination is Agda's ability to track the *depth* of defined coinductive data, allowing only recursive calls with strictly smaller depth. This condition ensures that the function does not consume more data than it is required to produce.

Let's delve into a classic example of a coinductive type, the ``Stream``:

::

    record Stream : Set where
      coinductive
      field
        head : Nat
        tail : Stream

Similar to the datatype of natural numbers, streams are represented as a single size variable ``t₀`` in our size type system. Here, our focus is on the recursive field, tail. In Agda, fields are treated as functions, specifically, we have ``tail : Stream → Stream``. The size encoding of fields is dual to constructors: ``tail`` is represented as ``t₁ → t₂``, where ``t₂ < t₁``. Notably, the *codomain* is smaller than the *domain*, which is the opposite of constructors. This makes sense since projections decrease the size of the applied record.

Mirroring pattern-matching, coinductive functions are defined using *copattern matching*. Consider a simple function that generates an endless stream of zeros:

::

    repeat : Stream
    repeat Stream.head = zero
    repeat Stream.tail = repeat

This function is encoded as a single size variable ``t₃``. Let's focus on the second branch repeat ``Stream.tail = repeat``, as it is the only branch relevant from a termination perspective.

Record projections, like data constructors, introduce rigid variables during copattern matching. Here, the rigid variables are ``t₃`` and ``t₄`` with ``t₄ < t₃``, where ``t₃ → t₄`` represents the adjusted size type of tail, initially ``t₁ → t₂``. We see that the role of codomain in the size signature is more critical here than in inductive functions.

Considering the usage of ``tail``, the expected type of the body of the second clause is ``Stream`` or, as a size type, t₄. The body contains a single recursive call to repeat, which, as following the logic of the previous section, introduces a fresh size type ``t₅``. Notably, since ``Stream`` is a coinductive type, it monotonically decreases in its size, allowing "deeper" streams to be used wherever "shallower" streams are required. Therefore, the desired constraint is ``t₄ ≤ t₅`` — any stream with depth greater or equal to ``t₄`` suffices here.

In this environment, the only flexible variable is ``t₅``, which can be assigned to ``t₄``. Since ``t₄ < t₃``, the recursive call to repeat is used with a smaller depth than the enclosing repeat, indicating that the definition is productive—it does not consume more of itself than necessary for production.

.. _type-based-termination-checking-size-preservation:

Size preservation
-----------------

We've previously observed that the polymorphic function ``id`` is understood by the type-based termination checker to return a term of the same size as the accepted one. This understanding is derived informally by examining the polymorphic type signature of ``id``. However, what if ``id`` had a non-polymorphic type ``Nat → Nat``? Can we make any judgement about its behavior?

This scenario is covered by another crucial aspect of the type-based termination checker, known as the ability to detect dependencies between sizes in signatures. This feature is referred to as *size preservation*.

While size checking a term, the checker can analyze dependencies between flexible and rigid size variables, concluding that some of them can be considered equal.

For example, consider the following set of functions:

::

      g : Nat → Nat
      g zero    = zero
      g (suc n) = suc (g n)

      h : Nat → Nat
      h zero    = suc zero
      h (suc n) = suc (h n)

After the invocation of ``g``, the constructed natural number is built with the same number of constructors as the passed number. This allows us to conclude that ``g`` preserves the size of the input in its output. In contrast, ``h`` returns a larger number, indicating that ``h`` is not size-preserving. The type-based checker can comprehend this and adjusts the size types of ``g`` accordingly. If its original size type was ``t₁ → t₂``, then the modified type would be ``t₁ → t₁`` to reflect the size-preservation behavior. It's noteworthy that for inductive functions, size preservation attempts to check whether there is a size in the codomain of the signature that can be equal to some size in the domain.

As a consequence, the following function can pass the termination check:

::

      plus : Nat → Nat → Nat
      plus zero    m = m
      plus (suc n) m = suc (plus (g n) m) -- note 'g' here

Another interesting application of size preservation can be found in combination with coinductive functions. For coinduction, size preservation seeks to determine whether it is possible to assign a fixed *codomain* size to some of the *domain* sizes. In other words, inductive definitions can be size-preserving in their output, while coinductive definitions can be size-preserving in their input.

For example, consider a coinductive function ``zipWith`` (with polymorphic streams):

::

    zipWith : {A B C : Set} → (A → B → C) → Stream A → Stream B → Stream C
    zipWith f s1 s2 .head = f (s1 .head) (s2 .head)
    zipWith f s1 s2 .tail = zipWith f (s1 .tail) (s2 .tail)

Here, the depth of the returned ``Stream C`` is the same as the requested depth of incoming ``s1`` and ``s2``. The type-based termination checker recognizes this, concluding that all three ``s1``, ``s2``, and the returned stream share the same size variable. We can assume that ``zipWith`` has size signature ``t₀ → t₀ → t₀`` (we shall consistently avoid the explanation of how polymorphism is handled in size types).

Given size-preserving ``zipWith``, we are able to define an infinite stream of Fibonacci numbers:

::

   fib : Stream Nat
   fib .head = zero
   fib .tail .head = suc zero
   fib .tail .tail = zipWith plus fib (fib .tail)

This function passes termination checking. Let's figure out what is happening here by dissecting the third clause.

Assume that ``fib`` is encoded as ``t₀``. The first copattern projection of tail brings a rigid size variable ``t₁``, and the second projection results in ``t₂``, which is also the expected type of the clause. Now, let a fresh size type of ``zipWith`` be ``t₃ → t₃ → t₃``; the size type of the first ``fib`` is ``t₄``, and the size type of the second ``fib`` (the projected one) is ``t₅``. Since the second ``fib`` is projected, we also have a fresh flexible size variable ``t₆`` with the requirement ``t₆ < t₅``. Given that all sizes represent coinductive definitions, we obtain a set of constraints ``t₂ ≤ t₃``, ``t₃ ≤ t₄``, ``t₃ ≤ t₆``, ``t₆ < t₅``. A suitable solution would be ``t₃ := t₂``, ``t₄ := t₂``, ``t₅ := t₁``, ``t₆ := t₂``. Both fibs are called with a size variable smaller than the top-level one (``t₂`` and ``t₁`` respectively), indicating that ``fib`` is productive. Note that size preservation is crucial here; otherwise, ``t₄`` and ``t₅`` would be disconnected from ``t₂``, implying that they have no suitable assignment among rigid variables.

As a final note, we address performance considerations. Currently, size-preservation analysis is the slowest part of the type-based termination checker. If you suspect that it causes a slowdown, you can specify ``--no-size-preservation``, disabling the analysis while retaining the rest of the type-based termination checker. Nevertheless, there are plans to improve its performance.

.. _type-based-termination-checking-size-limitations:

Limitations
-----------

The most significant limitation of the current implementation is rooted in the fact that the size type system relies on System Fω, while the target language of Agda is dependently-typed. In cases where a type signature of a function involves large elimination, it is likely that the type-based termination checker will encounter difficulties. This limitation arises because dependent types introduce additional complexity to the underlying theory, which was initially developed for a variant of System Fω. Further details on the semantical framework can be explored in :ref:`[1]<type-based-termination-checking-references>`.

The semantical framework used in the type-based termination checker is a variant of *sized types*. However, the sized types in Agda do not interact with the type-based termination checker. This stems partly from the complexity and unsoundness of sized types, whereas the type-based termination checker utilizes an intentionally restricted version of them. Presently, sized types serve as a means to manually address termination issues, although there are plans for the potential for interaction between type-based termination and sized types in the future.

It is known that the type-based termination checking is unsound when used in conjunction with univalence (and, more broadly, it is sensitive to the theory, meaning any postulate may compromise soundness). The reason lies in the fact that a function such as ``transport : A ≡ A → A → A`` can no longer be considered size-preserving. This is because the underlying isomorphism of ``Z ≡ Z`` (integer numbers) might increase the size of an argument of transport, while type-based termination would consider the size to remain unchanged.


.. _type-based-termination-checking-references:

References
----------

[1] Philip Wadler -- `Theorems for free!
<https://www.cse.chalmers.se/~abela/lehre/SS07/Typen/wadler89theorems.pdf>`_

[2] Andreas Abel, Brigitte Pientka -- `Well-founded recursion with copatterns and sized types.
<https://www.cambridge.org/core/journals/journal-of-functional-programming/article/wellfounded-recursion-with-copatterns-and-sized-types/39794AEA4D0F5003C8E9F88E564DA8DD>`_

