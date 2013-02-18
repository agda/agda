-- {-# OPTIONS -v tc.term.args:30 -v tc.meta:50 #-}
module Issue795 where

data Q (A : Set) : Set where

F : (N : Set → Set) → Set₁
F N = (A : Set) → N (Q A) → N A

postulate
   N : Set → Set
   f : F N
   R : (N : Set → Set) → Set
   funny-term : ∀ N → (f : F N) → R N

-- This should work now:  WAS: "Refuse to construct infinite term".
thing : R N
thing = funny-term _ (λ A → f _)
  -- funny-term ?N : F ?N -> R ?N
  -- funny-term ?N : ((A : Set) -> ?N (Q A) -> ?N A) -> R ?N
  -- A : F ?N |- f (?A A) :=> ?N (Q (?A A)) -> ?N (?A A)
  --   |- λ A → f (?A A) <=:  (A : Set) -> N (Q A) -> N A


{- What is happening here?

Agda first creates a (closed) meta variable

  ?N : Set -> Set

Then it checks

  λ A → f ?   against type F ?N = (A : Set) -> ?N (Q A) -> ?N A

(After what it does now, it still needs to check that

  R ?N  is a subtype of R N

It would be smart if that was done first.)

In context A : Set, continues to check

  f ?  against type  ?N (Q A) -> ?N A

Since the type of f is F N = (A : Set) -> N (Q A) -> N A, the created meta,
dependent on A : Set is

  ?A : Set -> Set

and we are left with checking that the inferred type of f (?A A),

  N (Q (?A A)) -> N (?A A)

is a subtype of

  ?N (Q A) -> ?N A

This yields two equations

  ?N (Q A) = N (Q (?A A))

  ?N A     = N (?A A)

The second one is solved as

  ?N = λ z → N (?A z)

simpliying the remaining equation to

  N (?A (Q A)) = N (Q (?A A))

and further to

  ?A (Q A) = Q (?A A)

The expected solution is, of course, the identity, but it cannot be
found mechanically from this equation.

At this point, another solution is ?A = Q.
In general, any power of Q is a solution.

If Agda postponed here, it would come to the problem

  R ?N  =  R N

simplified to ?N = N and instantiated to

  λ z → N (?A z)  =  N

This would solve ?A to be the identity.
-}
