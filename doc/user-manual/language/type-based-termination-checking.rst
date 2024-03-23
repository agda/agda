..
  ::
  module language.type-based-termination-checking where

      open import Agda.Builtin.Nat
      open import Agda.Builtin.List

.. _type-based-termination-checking:

*******************************
Type-Based Termination Checking
*******************************

.. note::
   Type-based termination checking is based on a master's thesis described in :ref:`[1]<type-based-termination-checking-references>`.

Sometimes the default termination checker in Agda may seem too weak. Let's explore this in the context of defining a finitely-branching tree:

::

      data RoseTree (A : Set) : Set where
        rose : A → List (RoseTree A) → RoseTree A

      mapRose : {A B : Set} → (A → B) → RoseTree A → RoseTree B
      mapRose f (rose a children) = rose (f a) (map (mapRose f) children)

Intuitively, we observe that ``children`` represents a list of "smaller" rose trees. When we call ``map (mapRose f) children``, we effectively apply ``mapRose f`` to each of these smaller trees. Thus, the function ``mapRose`` terminates, as all recursive calls accept trees smaller than the initial argument of ``mapRose``.

However, ``mapRose`` does not adhere to the pattern of syntactic recursion, as it is passed to another function instead of being directly called on a structurally smaller argument. Agda rejects such definitions because, instead of ``map``, an arbitrary function could be used. This arbitrary function might alter its arguments in unpredictable ways, rendering ``mapRose`` non-terminating.

In our case, we use ``map`` and trust it. The evidence for this trust lies in the type signature of ``map: {A' B' : Set} → (A' → B') → List A' → List B'``. According to this signature, map operates on arbitrary types, meaning it cannot construct a malicious ``RoseTree``. This property, known as parametricity, aligns with the logic of Agda, as described in :ref:`[2]<type-based-termination-checking-references>`.

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

It is important to note that the type-based termination checker requires preprocessing of all datatypes involved in the checking process. For the provided definitions, the files containing ``Nat``, ``List``, and ``RoseTree`` should all be type-checked with the ``--type-based-termination`` option enabled.

By default, type-based termination is disabled. You can also explicitly disable it by specifying ``--no-type-based-termination``.

Additionally, there's an option ``--(no-)syntax-based-termination`` that enables or disables the default syntax-based termination checker. This option can be useful if you wish to exclusively experiment with the type-based termination.

Another option is ``--(no-)size-preservation``, explained
:ref:`here<type-based-termination-checking-size-preservation>`.

For a deeper understanding of the internal behavior of the type-based termination checker, you can use the verbosity option ``term.tbt`` with different levels. An example of usage is ``{-# OPTIONS -v term.tbt:40 #-}`` in the file header. This option dumps the output of the checker. Note that Agda needs to be built in debug mode to print any verbose data.


.. _type-based-termination-checking-inductive:

Inductive definitions
---------------------

The core principle of the type-based termination checking is still the requirement to perform recursive calls on structurally smaller arguments. However, as we saw above, the calls may happen under some higher-order function.

Given a datatype, Agda first pre-processes its signature and constructor to assert dependencies between terms. For example, consider a type of natural numbers.

::

      data Nat : Set where
        zero : Nat
        suc  : Nat → Nat

Under type-based termination checking, Agda asserts that ``suc`` constructs "bigger" numbers from smaller ones.

Pattern-matching is still required in recursive definitions. During the process of pattern-matching, Agda obtains "smaller" terms in the scope, and then it can check whether recursive calls are performed on small arguments.

.. _type-based-termination-checking-coinduction:

Coinductive definitions
-----------------------

The type-based termination checker in Agda extends its default guardedness checker to support coinductive definitions. The fundamental idea behind coinductive type-based termination is Agda's ability to track the *depth* of defined coinductive data, allowing only recursive calls with strictly smaller depth. This condition ensures that the function does not consume more data than it is required to produce.

We shall illustrate this on a classic example of a coinductive type, the ``Stream``:

::

    record Stream : Set where
      coinductive
      field
        head : Nat
        tail : Stream

    open Stream

Here, our focus is on the recursive field, ``tail``. In Agda, fields are represented as functions, which in this case would be ``tail: Stream → Stream``. For fields, the *codomain* is smaller than the *domain*, which is the opposite of constructors. This makes sense since projections decrease the size of the applied record.

Mirroring pattern-matching, coinductive functions are defined using *copattern matching*. Consider a simple function that generates an endless stream of zeros:

::

    repeat : Stream
    repeat .head = zero
    repeat .tail = repeat

We shall again focus on the second branch ``Stream.tail = repeat``, as it is the only branch relevant from a termination perspective. Assume that ``repeat`` produces a stream of depth ``n``. According to the definition of ``tail``, this branch needs to construct a stream of depth ``m < n`` *for any* ``m``. A direct recursive call to ``repeat`` suffices here: it can be assumed that the inner ``repeat`` is used with the depth ``m``. Now, since the stream-returning function is defined in terms of "shallower" streams, Agda considers it terminating, as an arbitrary number of unfoldings for ``repeat`` will terminate.

Now consider the following function:

::

    badRepeat : Stream
    badRepeat .head = zero
    badRepeat .tail = badRepeat .tail

The difference here is that now inner ``badRepeat`` is projected. The logic from the previous paragraph does not apply here: if ``badRepeat .tail`` is of depth ``m``, then the inner ``badRepeat`` must have depth bigger than ``m``, say ``k``. There is no evidence that ``k < n``, so Agda rejects this definition as non-terminating. Indeed, it can be unfolded infinitely, which destroys strong normalization.

.. _type-based-termination-checking-mutual-induction-coinduction:

Induction-Coinduction
-----------------------

One of the features of the type-based termination checker is the support of mutually defined inductive and coinductive types.

We shall illustrate it on the stream processors.

::

    -- The inductive part of stream processors
    -- This datatype allows choosing to consume incoming stream or
    -- produce an element of a new one.
    data   SPμ (A B : Set) : Set
    -- The coinductive part of stream processors
    -- This datatype carries infinite behavior of this class.
    record SPν (A B : Set) : Set

    data SPμ A B where
      get : (A → SPμ A B) → SPμ A B -- Consumes an element of the incoming stream
      put : B → SPν A B → SPμ A B   -- Produces an element of the constructed stream

    record SPν A B where
      coinductive
      field force : SPμ A B

    open SPν

This datatype can be understood differently depending on the order of fixpoint operators in its formal definition. The two meanings that can be given here are
``ν SPν. μ SPμ. (A → SPμ) + (B ⨯ SPν)`` and ``μ SPμ. ν SPν. (A → SPμ) + (B ⨯ SPν)``. There is a substantial difference here. The first interpretation means that the stream processor infinitely produces ``B``, consuming a finite number of ``A``s between two productions. The second interpretation means that the stream processor may consume only finite number of ``A``s, and between each two consumptions it is allowed to produce infinite number of ``B``s. It is natural to select the first interpretation for stream processors, and that's what the type-based termination checker does.

This behavior can be reflects with the use of Agda's sized types:

::

    data   SPμ (i j : Size) (A B : Set) : Set
    record SPν (i : Size) (A B : Set) : Set

    data SPμ i j A B where
      get : {k : Size< j} → (A → SPμ i k A B) → SPμ i j A B
      put : B → SPν i A B → SPμ i j A B

    record SPν i A B where
      coinductive
      field force : {k : Size< i} → SPμ k ∞ A B

The following functions pass termination checking. We shall explain why ``runSPμ`` is a terminating function.

::

    runSPμ : {A B : Set} → SPμ A B → Stream A → Stream B
    runSPμ (put b spν) s .hd = b
    runSPμ (put b spν) s .tl = runSPμ (SPν.force spν) s
    runSPμ (get f) s = runSPμ (f (s .hd)) (s .tl)

    runSPν : {A B : Set} → SPν A B → Stream A → Stream B
    runSPν spν s = runSPμ (SPν.force spν) s


In the second clause, the list of copatterns contains a coinductive projection ``tl``. This means that if ``runSPμ`` defines a stream of depth ``n``, then the body ``runSPμ (SPν.force spν) s`` must define a stream of depth ``m < n``. Since ``runSPμ`` is not wrapped into any projection, Agda assumes that this corecursive call defines a stream of depth ``m``, which means that this clause cannot be unfolded infinitely.

In the third clause, there are no coinductive projections among copatterns. If ``runSPμ`` defines a stream of depth ``n``, here Agda assumes that ``runSPμ (f (s .hd)) (s .tl)`` also defines a stream of depth ``n``. This fact alone is not enough to prove termination: after all, the definition of ``runSPμ`` can be unfolded to the third clause infinitely, since ``n`` does not decrease during unfolding. However, ``runSPμ`` has also an inductive argument, which decreases with each call. It means that the third clause preserves the depth of the defined stream, but it decreases the inductive size of the accepted ``SPμ``.

Now we see that the unfolding of the first clause strictly decreases the depth of the stream, and the unfolding of the second clause preserves the depth of the stream, but strictly decreases the inductive size of ``SPμ``. This kind of lexicographical induction allows Agda to deduce that ``runSPμ`` terminates.

In general, if there is a set of mutually-inductive-coinductive datatypes, then the type-based checker provides the following encoding for them: there is a common size variable for all definitions that corresponds to coinductive part of the definition, and this variable can be decreased only by a coinductive projection. For inductive datatypes, there is additionally another size variable, that corresponds to the inductive part of the definition, and it can be decreased only by pattern-matching on an inductive constructor. This encoding can be represented in terms of Agda's sized types:

::

    data D1 (i j : Size) ... : ... → Set
    data D2 (i j : Size) ... : ... → Set
    ...
    data Dn (i j : Size) ... : ... → Set
    data R1 (i : Size)   ... : ... → Set
    data R2 (i : Size)   ... : ... → Set
    data Rm (i : Size)   ... : ... → Set

    data D i j ... where
      c1 : {j' : Size< j} → ... → Dk i j' → ... → D i j ...
      c2 : ... → Rk i → ... → D i j ...
      ...

    record Rn i ... where
      coinductive
      field
      f1 : {i' : Size< i} → ... → Rk i'
      f2 : {i' : Size< i} → ... → Dk i' ∞
      ...



.. _type-based-termination-checking-size-preservation:

Size preservation
-----------------

We've previously observed that the polymorphic function ``id`` is understood by the type-based termination checker to return a term of the same size as the accepted one. This understanding is derived informally by examining the polymorphic type signature of ``id``. However, what if ``id`` had a non-polymorphic type ``Nat → Nat``? Can we make any judgment about its behavior?

This scenario is covered by another crucial aspect of the type-based termination checker, known as the ability to detect dependencies between sizes in signatures. This feature is referred to as *size preservation*.

As an example example, consider the following function:

::

      minus : Nat → Nat → Nat
      minus zero x = zero
      minus x zero = x
      minus (suc x) (suc y) = minus x y

We see that in the first two branches, the result of the function is equal to the first argument. In particular, we see that the "size" of the first argument is preserved in the output. Assuming that this function returns natural numbers of size not bigger than the first argument, we can also analyze the third branch and confirm this assumption. The type-based checker can comprehend this and adjust the size types of ``minus``.

This behavior has useful consequences. For example, consider a function of division for two natural numbers. We can write this function in Agda meaning that number ``x`` is divided on ``y + 1``. With the help of size preservation, the following function passes termination check:

::

      div : Nat → Nat → Nat
      div zero    y = zero
      div (suc x) y = suc (div (minus x y) y)

Another interesting application of size preservation can be found in combination with coinductive functions. For coinduction, size preservation seeks to determine whether it is possible to assign a fixed *codomain* size to some of the *domain* sizes. In other words, inductive definitions can be size-preserving in their output, while coinductive definitions can be size-preserving in their input.

For example, consider a coinductive function ``zipWith``:

::

    zipWith : (Nat → Nat → Nat) → Stream → Stream → Stream
    zipWith f s1 s2 .head = f (s1 .head) (s2 .head)
    zipWith f s1 s2 .tail = zipWith f (s1 .tail) (s2 .tail)

Here, the depth of the returned ``Stream`` is the same as the requested depth of incoming ``s1`` and ``s2``. The type-based termination checker recognizes this, concluding that all three ``s1``, ``s2``, and the returned stream share the same size variable.

Given size-preserving ``zipWith``, Agda is able to define an infinite stream of Fibonacci numbers:

::

   fib : Stream
   fib .head = zero
   fib .tail .head = suc zero
   fib .tail .tail = zipWith plus fib (fib .tail)

This function passes termination checking. We shall explain the logic of Agda for the third clause.

Following our intuition with coinductive functions, the are three depth parameters ``k < m < n``, where the outer stream is of depth ``n``, and to pass checking the third clause should return the stream of depth at least ``k``. If the first inner ``fib`` is used with the depth ``k``, and the second ``fib`` is used with the depth ``m`` (note, that the smallest available depth for ``fib .tail`` is ``k``, hence ``fib`` must use something bigger, which is ``m``), then the size-preserving ``zipWith`` returns a stream of size ``k``, which is indeed what is required from it. Now we see that both recursive calls to ``fib`` are performed with depths ``k`` and ``m``, which are smaller than ``n``. Agda concludes that this function is terminating.

Size preservation is tightly coupled with polarities. Given a function signature, all occurrences of *negative inductive* and *positive coinductive* variables are considered as input, and they serve as possible candidates for size preservation analysis. On the other hand, all *positive inductive* and *negative coinductive* variables are considered as output, and a function signature may be size-preserving precisely in them. For example, consider the following definition:

::

    foo : {A : Set} → (Nat → A) → Nat → A
    foo f x = f x



Here, the first ``Nat`` in ``foo`` is in a doubly-negative position, which means that the position is positive, and ``foo`` can be size-preserving in the first ``Nat``. From the definition we see that it is indeed the case. One application of this fact is that the following function passes termination check:

::

    bar : Nat → Nat
    bar zero = zero
    bar (suc n) = foo bar n

As a final note, we address performance considerations. Currently, size-preservation analysis is the slowest part of the type-based termination checker. If you suspect that it causes a slowdown, you can specify ``--no-size-preservation``, disabling the analysis while retaining the rest of the type-based termination checker. Nevertheless, there are plans to improve its performance.

.. _type-based-termination-checking-size-limitations:

Limitations
-----------

The most significant limitation of the current implementation is rooted in the fact that the size type system relies on System Fω, while the target language of Agda is dependently-typed. In cases where a type signature of a function involves large elimination, it is likely that the type-based termination checker will encounter difficulties. This limitation arises because dependent types introduce additional complexity to the underlying theory, which was initially developed for a variant of System Fω. Further details on the semantical framework can be explored in :ref:`[3]<type-based-termination-checking-references>`.

The semantical framework used in the type-based termination checker is a variant of *sized types*. However, the sized types in Agda do not interact with the type-based termination checker. This stems partly from the complexity and unsoundness of sized types, whereas the type-based termination checker utilizes an intentionally restricted version of them. Presently, sized types serve as a means to manually address termination issues, although there are plans for the potential for interaction between type-based termination and sized types in the future.

.. _type-based-termination-checking-references:

References
----------

[1] Kanstantsin Nisht -- `Type-Based Termination Checking in Agda.
<https://knisht.github.io/agda/msc.pdf>`_

[2] Philip Wadler -- `Theorems for free!
<https://www.cse.chalmers.se/~abela/lehre/SS07/Typen/wadler89theorems.pdf>`_

[3] Andreas Abel, Brigitte Pientka -- `Well-founded recursion with copatterns and sized types.
<https://www.cambridge.org/core/journals/journal-of-functional-programming/article/wellfounded-recursion-with-copatterns-and-sized-types/39794AEA4D0F5003C8E9F88E564DA8DD>`_
