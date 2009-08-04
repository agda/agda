
-- This module introduces implicit arguments.

module Introduction.Implicit where

-- In Agda you can omit things that the type checker can figure out for itself.
-- This is a crucial feature in a monomorphic language, since you would
-- otherwise be overwhelmed by type arguments.

-- Let's revisit the identity function from 'Introduction.Basics'.

id' : (A : Set) -> A -> A
id' A x = x

-- Since Agda is monomorphic we have to take the type A as an argument. So when
-- using the identity function we have to provide the type explicitly.

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

one : Nat
one = id' Nat (suc zero)

-- Always having to provide the type argument to the identity function would of
-- course be very tedious, and seemingly unnecessary. We would expect the type
-- checker to be able to figure out what it should be by looking at the second
-- argument. And indeed the type checker can do this.

-- One way of indicating that the type checker will have figure something out
-- for itself is to write an underscore (_) instead of the term. So when
-- applying the identity function we can write

two : Nat
two = id' _ (suc one)

-- Now the type checker will try to figure out what the _ should be, and in
-- this case it will have no problems doing so. If it should fail to infer the
-- value of an _ it will issue an error message.

-- In the case of the identity function we expect the type argument to always
-- be inferrable so it would be nice if we could avoid having to write the _.
-- This can be achieved by declaring the first argument as an implicit
-- argument.

id : {A : Set} -> A -> A        -- implicit arguments are enclosed in curly braces
id x = x  -- now we don't have to mention A in the left-hand side

three : Nat
three = id (suc two)

-- If, for some reason, an implicit argument cannot be inferred it can be given
-- explicitly by enclosing it in curly braces : 

four : Nat
four = id {Nat} (suc three)

-- To summarise we give a bunch of possible variants of the identity function
-- and its use.

-- Various definitions of the identity function. Definitions 0 through 3 are
-- all equivalent, as are definitions 4 through 6.

id0 : (A : Set) -> A -> A
id0 A x = x

id1 : (A : Set) -> A -> A
id1 _ x = x     -- in left-hand sides _ means "don't care"

id2 : (A : Set) -> A -> A
id2 = \A x -> x

id3 = \(A : Set)(x : A) -> x  -- the type signature can be omitted for definitions
                          -- of the form x = e if the type of e can be
                          -- inferred.

id4 : {A : Set} -> A -> A
id4 x = x

id5 : {A : Set} -> A -> A
id5 {A} x = x

id6 : {A : Set} -> A -> A
id6 = \x -> x

id7 = \{A : Set}(x : A) -> x

-- id8 : {A : Set} -> A -> A
-- id8 = \{A} x -> x        -- this doesn't work since the type checker assumes
                            -- that the implicit A has been has been omitted in
                            -- the left-hand side (as in id6).

-- Various uses of the identity function.
zero0 = id0 Nat zero
zero1 = id0 _   zero  -- in right-hand sides _ means "go figure"

zero2 = id4       zero
zero3 = id4 {Nat} zero
zero4 = id4 {_}   zero  -- This is equivalent to zero2, but it can be useful if
                        -- a function has two implicit arguments and you need
                        -- to provide the second one (when you provide an
                        -- implicit argument explicitly it is assumed to be the
                        -- left-most one).

-- In this module we have looked at implicit arguments as a substitute for
-- polymorphism. The implicit argument mechanism is more general than that and
-- not limited to inferring the values of type arguments. For more information
-- on implicit arguments see, for instance
--  'Introduction.Data.ByRecursion'

