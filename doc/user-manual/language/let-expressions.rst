.. _let-expressions:

***************
Let Expressions
***************

There are two ways of declaring a local definition in Agda

- let-expressions
- where-expressions

let-expressions
---------------
let-expressions are used to define an abbreviation. In other words, the expression that we define in a let-expression can neither be recursive nor defined by pattern matching.

let-expressions have the general form
::

  let f : A1 -> … -> An -> A
      f x1 … xn= e
  in e’

Example
::

  f : Nat
  f =  let h : Nat -> Nat
           h m = succ (succ m)
       in h zero + h (succ zero)

where-expressions
-----------------
We could use where-expression to define macros as well, but we could also use where-expression to define recursive definitions by pattern matching.

where-expressions have the general form
::

  e
  where f : A1 -> … -> An -> A
        f p11 … p1n= e1
        …
        …
        f pm1 … pmn= em

Here, the ``pij`` are patterns of the corresponding types and ``ei`` is an expression that can contain occurrences of ``f``.
Functions defined with a where-expression must follow the rules for general definitions by pattern matching.

Example
::

  reverse : {A : Set} -> List A -> List A
  reverse {A} xs = rev xs []
     where rev : List A -> List A -> List A
           rev [] ys = ys
           rev (x :: xs) ys = rev xs (x :: ys)

Variable scope
--------------
It is important to notice that only variables that appear to the left of the equation that defines a local definition are in the scope of the local definition, independently of whether we use let- or where-expressions.

Proving properties
------------------
Be aware that local definitions are exactly that, local. Then, we will not be able to prove any property about them which in turn will make it difficult to prove properties about the function that defines the local expression.

Therefore, it could be better in some situations to define auxiliary functions as private to the module we are working in; hence, they won’t be visible in any module that imports this module but it will allow us to prove some properties about them.
::

  private
     rev : {A : Set} -> List A -> List A -> List A
     rev [] ys = ys
     rev (x :: xs) ys = rev xs (x :: ys)

  reverse' : {A : Set} -> List A -> List A
  reverse' xs = rev xs []

More Examples
-------------
Using let-expression
::

  tw-map : {A : Set} -> List A -> List (List A)
  tw-map {A} xs = let twice : List A -> List A
                      twice xs = xs ++ xs
                  in map (\x -> twice [ x ]) xs

Same definition but with less type information
::

  tw-map' : {A : Set} -> List A -> List (List A)
  tw-map' {A} xs = let twice : _
                       twice xs = xs ++ xs
                   in map (\x -> twice [ x ]) xs

Same definition but with a where-expression
::

  tw-map'' : {A : Set} -> List A -> List (List A)
  tw-map'' {A} xs =  map (\x -> twice [ x ]) xs
     where twice : List A -> List A
           twice xs = xs ++ xs

Even less type informaiton using let
::

  0-_ : Nat -> List Nat
  0- zero = [ zero ]
  0- (succ n) = let sing = [ succ n ]
                in sing ++ 0- n

Same definition using where
::

  0'-_ : Nat -> List Nat
  0'- zero = [ zero ]
  0'- (succ n) = sing ++ 0'- n
     where  sing = [ succ n ]

More than one definition in a let
::

  h : Nat -> Nat
  h n = let add2 : Nat
            add2 = succ (succ n)

            twice : Nat -> Nat
            twice m = m * m

        in twice add2

More than one definition in a where
::

  g : Nat -> Nat
  g n = fib n + fact n
   where fib : Nat -> Nat
         fib zero = succ zero
         fib (succ zero) = succ zero
         fib (succ (succ n)) = fib (succ n) + fib n

         fact : Nat -> Nat
         fact zero = succ zero
         fact (succ n) = succ n * fact n

Combining let and where
::

  k : Nat -> Nat
  k n = let aux : Nat -> Nat
            aux m = pred (g m) + h m
        in aux (pred n)
    where pred : Nat -> Nat
          pred zero = zero
          pred (succ m) = m
