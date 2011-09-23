{-

  In order to solve the metavariables in this example
  we need to solve a constraint of the form

    _1 := unit₂ (_2 y)

  With the flex removal feature the occurs check will
  spot the bad variable 'y' in the instantiation and
  remove it by instantiating

    _2 := λ y → _3

  for a fresh metavariable _3. The instantiation of _1
  can then proceed.

-}
module FlexRemoval where

record Unit : Set where

data Unit₂ : Set where
 unit₂ : Unit → Unit₂

mutual

 data D : Set where
   c₁ : D
   c₂ : (x : Unit₂) → (Unit → D₂ x) → D

 D₂ : Unit₂ → Set
 D₂ (unit₂ x) = D

foo : D
foo = c₂ _ (λ y → c₁)

{- 2011-04-05 Andreas

This test case and the explanation is no longer up to date.  
What happens is

  _2 y : Unit  

is solved by eta-expansion

  _2 = λ y -> record {}

and then 

  _1 = unit₂ (record {})

is in solved form.

-}