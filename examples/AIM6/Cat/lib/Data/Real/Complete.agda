
module Data.Real.Complete where

import Prelude
import Data.Real.Gauge
import Data.Rational

open Prelude
open Data.Real.Gauge
open Data.Rational

Complete : Set -> Set
Complete A = Gauge -> A

unit : {A : Set} -> A -> Complete A
unit x ε = x

join : {A : Set} -> Complete (Complete A) -> Complete A
join f ε = f ε2 ε2
  where
    ε2 = ε / fromNat 2

infixr 10 _==>_

data _==>_ (A B : Set) : Set where
  uniformCts : (Gauge -> Gauge) -> (A -> B) -> A ==> B

modulus : {A B : Set} -> (A ==> B) -> Gauge -> Gauge
modulus (uniformCts μ _) = μ

forgetUniformCts : {A B : Set} -> (A ==> B) -> A -> B
forgetUniformCts (uniformCts _ f) = f

mapC : {A B : Set} -> (A ==> B) -> Complete A -> Complete B
mapC (uniformCts μ f) x ε = f (x (μ ε))

bind : {A B : Set} -> (A ==> Complete B) -> Complete A -> Complete B
bind f x = join $ mapC f x

mapC2 : {A B C : Set} -> (A ==> B ==> C) -> Complete A -> Complete B -> Complete C
mapC2 f x y ε = mapC ≈fx y ε2
  where
    ε2  = ε / fromNat 2
    ≈fx = mapC f x ε2

_○_ : {A B C : Set} -> (B ==> C) -> (A ==> B) -> A ==> C
f ○ g = uniformCts μ h
  where
    μ = modulus f ∘ modulus g
    h = forgetUniformCts f ∘ forgetUniformCts g

constCts : {A B : Set} -> A -> B ==> A
constCts a = uniformCts (const $ fromNat 1) (const a)

