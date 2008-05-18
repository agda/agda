
module Logic.ChainReasoning where

module Mono where

  module Homogenous
    { A : Set }
    ( _==_ : A -> A -> Set )
    (refl  : (x : A) -> x == x)
    (trans : (x y z : A) -> x == y -> y == z -> x == z)
    where

    infix 2 chain>_
    infixl 2 _===_
    infix 3 _by_

    chain>_ : (x : A) -> x == x
    chain> x = refl _

    _===_ : {x y z : A} -> x == y -> y == z -> x == z
    xy === yz = trans _ _ _ xy yz

    _by_ : {x : A}(y : A) -> x == y -> x == y
    y by eq = eq

module Poly where

  module Homogenous
    ( _==_ : {A : Set} -> A -> A -> Set )
    (refl  : {A : Set}(x : A) -> x == x)
    (trans : {A : Set}(x y z : A) -> x == y -> y == z -> x == z)
    where

    infix 2 chain>_
    infixl 2 _===_
    infix 3 _by_

    chain>_ : {A : Set}(x : A) -> x == x
    chain> x = refl _

    _===_ : {A : Set}{x y z : A} -> x == y -> y == z -> x == z
    xy === yz = trans _ _ _ xy yz

    _by_ : {A : Set}{x : A}(y : A) -> x == y -> x == y
    y by eq = eq

  module Heterogenous
    ( _==_ : {A B : Set} -> A -> B -> Set )
    (refl  : {A : Set}(x : A) -> x == x)
    (trans : {A B C : Set}(x : A)(y : B)(z : C) -> x == y -> y == z -> x == z)
    where

    infix 2 chain>_
    infixl 2 _===_
    infix 3 _by_

    chain>_ : {A : Set}(x : A) -> x == x
    chain> x = refl _

    _===_ : {A B C : Set}{x : A}{y : B}{z : C} -> x == y -> y == z -> x == z
    xy === yz = trans _ _ _ xy yz

    _by_ : {A B : Set}{x : A}(y : B) -> x == y -> x == y
    y by eq = eq

  module Heterogenous1
    ( _==_ : {A B : Set1} -> A -> B -> Set1 )
    (refl  : {A : Set1}(x : A) -> x == x)
    (trans : {A B C : Set1}(x : A)(y : B)(z : C) -> x == y -> y == z -> x == z)
    where

    infix 2 chain>_
    infixl 2 _===_
    infix 3 _by_

    chain>_ : {A : Set1}(x : A) -> x == x
    chain> x = refl _

    _===_ : {A B C : Set1}{x : A}{y : B}{z : C} -> x == y -> y == z -> x == z
    xy === yz = trans _ _ _ xy yz

    _by_ : {A B : Set1}{x : A}(y : B) -> x == y -> x == y
    y by eq = eq

