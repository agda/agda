------------------------------------------------------------------------
-- Applicative functors
------------------------------------------------------------------------

-- Note that currently the applicative functor laws are not included
-- here.

module Category.Applicative where

open import Data.Unit
open import Category.Applicative.Indexed

RawApplicative : (Set -> Set) -> Set1
RawApplicative F = RawIApplicative {I = ⊤} (\_ _ -> F)

module RawApplicativeOps {F : Set -> Set}
                         (app : RawApplicative F)
                         where

  open RawIApplicative app public
