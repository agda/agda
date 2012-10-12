module PatternMatchingLambda where

data Bool : Set where
  true false : Bool

data Void : Set where

data _≡_ {A : Set}(x : A) : A -> Set where
  refl : x ≡ x

and : Bool -> Bool -> Bool
and = λ { true x → x ; false _ → false }


or : Bool -> Bool -> Bool
or x y = not (and (not x) (not y))
  where not : Bool -> Bool
        not = \ { true -> false ; false -> true }

iff : Bool -> Bool -> Bool -> Bool
iff = λ { true  x -> λ { true → true ; false → false } ;
          false x -> λ { true -> false ; false -> true }
        }

pattern-matching-lambdas-compute : (x : Bool) -> or true x ≡ true
pattern-matching-lambdas-compute x = refl

isTrue : Bool -> Set
isTrue = \ { true -> Bool ; false -> Void }

absurd : (x : Bool) -> isTrue x -> Bool
absurd = \ { true x -> x ; false () }

--carefully chosen without eta, so that pattern matching is needed
data Unit : Set where
  unit : Unit

isNotUnit : Unit -> Set
isNotUnit = \ { tt -> Void }

absurd-one-clause : (x : Unit) -> isNotUnit x -> Bool
absurd-one-clause = λ { tt ()}

data indexed-by-xor : (Bool -> Bool -> Bool) -> Set where
  c : (b : Bool) -> indexed-by-xor \ { true  true  -> false ;
                                       false false -> false ;
                                       _     _     -> true  }

-- won't work if the underscore is replaced with the actual value at the moment
f : (r : Bool -> Bool -> Bool) -> indexed-by-xor r -> Bool
f ._ (c b) = b

record Σ (A : Set)(B : A -> Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

fst : {A : Set}{B : A -> Set} -> (x : Σ A B) -> A
fst =  \ { (a , b) -> a }

snd : {A : Set}{B : A -> Set} -> (x : Σ A B) -> B (fst x)
snd = \ { (a , b) -> b }

record FamSet : Set1 where
  constructor _,_
  field
    A : Set
    B : A -> Set

ΣFAM : (A : Set)(B : A -> Set)(P : A -> Set)(Q : (x : A) -> B x -> P x -> Set) -> FamSet
ΣFAM A B P Q = (Σ A P , \ { (a , p) -> Σ (B a) (λ b → Q a b p) } )

--The syntax doesn't interfere with hidden lambdas etc:
postulate
  P : ({x : Bool} -> Bool) -> Set
  p : P (λ {x} → x)

--Issue 446: Absurd clauses can appear inside more complex expressions
data Box (A : Set) : Set where
  box : A → Box A

foo : {A : Set} → Box Void → A
foo = λ { (box ()) }
