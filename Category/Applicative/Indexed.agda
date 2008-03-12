------------------------------------------------------------------------
-- Indexed applicative functors
------------------------------------------------------------------------

-- Note that currently the applicative functor laws are not included
-- here.

module Category.Applicative.Indexed where

open import Data.Function
open import Category.Functor

IFun : Set -> Set1
IFun I = I -> I -> Set -> Set

record RawIApplicative {I : Set} (F : IFun I) : Set1 where
  infixl 4 _⊛_ _<⊛_ _⊛>_

  field
    pure : forall {i A} -> A -> F i i A
    _⊛_  : forall {i j k A B} -> F i j (A -> B) -> F j k A -> F i k B

  rawFunctor : forall {i j} -> RawFunctor (F i j)
  rawFunctor = record
    { _<$>_ = \g x -> pure g ⊛ x
    }

  private
    open module RF {i j : I} =
           RawFunctor (rawFunctor {i = i} {j = j})
           public

  _<⊛_ : forall {i j k A B} -> F i j A -> F j k B -> F i k A
  x <⊛ y = const <$> x ⊛ y

  _⊛>_ : forall {i j k A B} -> F i j A -> F j k B -> F i k B
  x ⊛> y = flip const <$> x ⊛ y
