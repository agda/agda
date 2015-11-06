.. _data-types:

**********
Data Types
**********

Example datatypes
=================

In the introduction we already showed the definition of the data type of natural numbers (in unary notation)::

    data Nat : Set where
	zero : Nat
	suc  : Nat → Nat

We give a few more examples. First the data type of truth values::

    data Bool : Set where
      true  : Bool
      false : Bool

Then the unit set::

    data True : Set where
	tt : True

The True set represents the trivially true proposition.::

    data False : Set where

The False set has no constructor and hence no elements. It represent the trivially false proposition.

Another example is the data type of non-empty  binary trees with natural numbers in the leaves::

    data BinTree : Set where
      leaf   : Nat → BinTree
      branch : BinTree → BinTree → BinTree

Finally, the data type of Brouwer ordinals::

    data Ord : Set where
      zeroOrd : Ord
      sucOrd  : Ord → Ord
      limOrd  : (Nat → Ord) → Ord

General form
============

The general form of the definition of a simple data type D is the following::

    data D : Set where
      c₁ : A₁
      ...
      cₙ : Aₙ

The name D of the data type and the names c₁, ..., cₙ of the
constructors must be new wrt the current signature and context.

Agda checks that A₁, ..., Aₙ : Set wrt the current signature
and context. Moreover, each Aᵢ has the form::

    (y₁ : B₁) → ... → (yₘ : Bₘ) → D

where an argument types Bᵢ of the constructors is either

* *non-inductive* (a *side condition*) and does not mention D at all, 

* or *inductive* and has the form::

    (z₁ : C₁) → ... → (zₖ : Cₖ) → D

where D must not occur in any Cⱼ.

Strict positivity
=================

The condition that D must not occur in any Cⱼ can be also phrased
as D must only occur **strictly positively** in Bᵢ.
 
Agda can check this positivity condition.

The strict positivity condition rules out declarations such as::

    data Bad : Set where
        bad : (Bad → Bad) → Bad
          A      B       C
        -- A is in a negative position, B and C are OK

since there is a negative occurrence of Bad in the type of the
argument of the constructor.  (Note that the corresponding data type
declaration of Bad is allowed in standard functional languages such as
Haskell and ML.).

Non strictly-positive declarations are rejected because one can write
a non-terminating function using them.

If the positivity check is disabled so that the above declaration of
Bad is allowed, it is possible to construct a term of the empty
type.::

    {-# OPTIONS --no-positivity-check #-}
    data ⊥ : Set where

    data Bad : Set where
        bad : (Bad → Bad) → Bad

    incon : ⊥
    incon = loop (bad (λ b → b))
	where
	    loop : (b : Bad) → ⊥
	    loop (bad f) = loop (f (bad f))


For more general information on termination see :ref:`termination-checking`.
