
-- This module introduces the basic structure of an Agda program.

{- Every Agda file contains a single top-level module. To make it possible to
   find the file corresponding to a particular module, the name of the file
   should correspond to the name of the module. In this case the module
   'Introduction.Basics' is defined in the file 'Introduction/Basics.agda'.
-}
module Introduction.Basics where

{- The top-level module contains a sequence of declarations, such as datatype
   declarations and function definitions. The most common forms of declarations
   are introduced below.

   A module can also contain sub-modules, see 'Introduction.Modules.SubModules'
   for more information.
-}

-- Agda can be used as a pure logical framework. The 'postulate' declaration
-- introduces new constants : 
postulate
  N : Set     -- Set is the first universe
  z : N
  s : N -> N  -- The independent function space is written A -> B

-- Using 'postulate' it is not possible to introduce new computation rules. A
-- better way is to introduce a datatype and define functions by pattern
-- matching on elements of the datatype.

-- A datatype is introduced with the 'data' keyword. All constructors of the
-- datatype are given with their types after the 'where'. Datatypes can be
-- parameterised (see 'Introduction.Data.Parameterised').

data Bool : Set where
  false : Bool
  true  : Bool

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- Functions over datatypes can be defined by pattern matching.

plus : Nat -> Nat -> Nat
plus  zero   m = m
plus (suc n) m = suc (plus n m)

-- With this definition plus (suc zero) (suc zero) will reduce to suc (suc
-- zero).

-- When defining mutually recursive functions you have to declare functions
-- before they can be called.

odd : Nat -> Bool

even : Nat -> Bool
even zero    = true
even (suc n) = odd n

odd zero    = false
odd (suc n) = even n

-- Agda is a monomorphic, but dependently typed, language. This means that
-- polymorphism is simulated by having functions take type arguments. For
-- instance, the polymorphic identity function can be represented as follows : 

id : (A : Set) -> A -> A        -- the dependent function space is written (x : A) -> B
id A x = x

one : Nat
one = id Nat (suc zero) -- a silly use of the identity function

-- To faithfully simulate a polymorphic function we would like to omit the type
-- argument when using the function. See 'Introduction.Implicit' for
-- information on how to do this.

-- Agda is both a programming language and a formal proof language, so we
-- expect to be able to prove theorems about our programs. As an example we
-- prove the very simple theorem n + 0 == n.

-- First we introduce datatypes for truth (a singleton type) and falsity (an
-- empty type).

data True : Set where   -- Here it would make sense to declare True to be a
  tt : True             -- Prop (the universe of propositions) rather than a
                        -- Set. See 'Introduction.Universes' for more
                        -- information.

data False : Set where  -- see 'Introduction.Data.Empty' for more information
                        -- on empty types.

-- Second, we define what it means for two natural numbers to be equal. Infix
-- operators are declared by enclosing the operator in _. See
-- 'Introduction.Operators' for more information.

_==_ : Nat -> Nat -> Set
zero  == zero  = True
zero  == suc m = False
suc n == zero  = False
suc n == suc m = n == m

-- Now we are ready to state and prove our theorem. The proof is by induction
-- (i.e. recursion) on 'n'.

thmPlusZero : (n : Nat) -> plus n zero == n   -- A function from a number n to
                                            -- P n can be seen as the
                                            -- proposition ∀ n. P n.
thmPlusZero  zero   = tt
thmPlusZero (suc n) = thmPlusZero n

{- In both branches the reduction makes the proof very simple. In the first
   case the goal is

    plus zero zero == zero    which reduces to
    zero == zero              and
    True

  In the second case we have

    plus (suc n) zero == suc n
    suc (plus n zero) == suc n
    plus n zero == n

  so the induction hypothesis (the recursive call) is directly applicable.
-}

