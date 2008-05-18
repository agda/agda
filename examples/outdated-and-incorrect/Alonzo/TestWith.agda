{-

        Agda Implementors' Meeting VI

                  Göteborg
             May 24 - 30, 2007


                Hello Agda!

                Ulf Norell

-}

-- Something which is rather useful is the ability to pattern match
-- on intermediate computations. That's where the with-construct comes
-- in.

module TestWith where

-- open import Nat
open import PreludeNat hiding(_==_; even; odd)
open import PreludeShow

{-

  Basic idea

-}

-- The basic principle is that you can add argument to your
-- function on the fly. For instance,

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A -> Maybe A

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

compare : (n m : Nat) -> Maybe (n == m)
compare  zero   zero   = just refl
compare (suc _) zero   = nothing
compare  zero  (suc _) = nothing
compare (suc n)(suc m) with compare n m
compare (suc n)(suc .n) | just refl = just refl
compare (suc n)(suc m)  | nothing   = nothing

-- To add more than one argument separate by |
silly : Nat -> Nat
silly zero = zero
silly (suc n) with n | n
silly (suc n) | zero | suc m = m  -- the values of the extra argument are
                                  -- not taken into consideration
silly (suc n) | _    | _     = n

{-

  The parity example

-}

-- This is a cute example of what you can do with with.

data Parity : Nat -> Set where
  even : (k : Nat) -> Parity (k * 2)
  odd  : (k : Nat) -> Parity (1 + k * 2)

parity : (n : Nat) -> Parity n
parity zero = even 0
parity (suc n) with parity n
parity (suc .(    k * 2)) | even k = odd k
parity (suc .(1 + k * 2)) | odd  k = even (suc k)

half : Nat -> Nat
half n with parity n
half .(    k * 2) | even k = k
half .(1 + k * 2) | odd  k = k


mainS = showNat (half 44)
{-

  What's next?

-}

-- Move on to: Modules.agda