-- Andreas, 2015-12-05 issue reported by Conor

-- {-# OPTIONS -v tc.cover.splittree:10 -v tc.cc:20 #-}

module Issue1734 where

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

record One : Set where constructor <>

data Two : Set where tt ff : Two

-- two : ∀{α}{A : Set α} → A → A → Two → A
two : (S T : Set) → Two → Set
two a b tt = a
two a b ff = b

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public

_+_ : Set -> Set -> Set
S + T = Sg Two (two S T)

data Twoey : Two -> Set where
  ffey  : Twoey ff
  ttey  : Twoey tt

postulate Thingy : Set

ThingyIf : Two -> Set
ThingyIf tt = Thingy
ThingyIf ff = One

thingy? : (b : Two) -> ThingyIf b -> Twoey b + One -> Thingy + One
thingy? .ff <> (tt , ffey) = ff , <>
thingy? .tt x  (tt , ttey) = tt , x
thingy? _   _  _           = ff , <>

-- WORKS: thingy? _   _  (ff , _   ) = ff , <>

{- Correct split tree

split at 2
|
`- Issue1734.Sg._,_ -> split at 2
   |
   +- Issue1734.Two.tt -> split at 2
   |  |
   |  +- Issue1734.Twoey.ffey -> split at 1
   |  |  |
   |  |  `- Issue1734.One.<> -> done, 0 bindings
   |  |
   |  `- Issue1734.Twoey.ttey -> done, 1 bindings
   |
   `- Issue1734.Two.ff -> done, 3 bindings

but clause compiler deviated from it:

thingy? b x p =
  case p of (y , z) ->
    case y of
      tt -> case x of
              <> -> case z of
                      ffey -> ff , <>
                      ttey -> tt , <>
              _  -> case z of
                      ttey -> tt , x
      _  -> ff , <>

compiled clauses (still containing record splits)
  case 2 of
  Issue1734.Sg._,_ ->
    case 2 of
      Issue1734.Two.tt ->
        case 1 of
          Issue1734.One.<> ->
            case 1 of
              Issue1734.Twoey.ffey -> ff , <>
              Issue1734.Twoey.ttey -> tt , <>
          _ -> case 2 of
                 Issue1734.Twoey.ttey -> tt , x
      _ -> ff , <>

-}

test1 : ∀ x → thingy? tt x (tt , ttey) ≡ tt , x
test1 = λ x → refl  -- should pass!

first-eq-works : ∀ x → thingy? ff x (tt , ffey) ≡ ff , x
first-eq-works = λ x → refl

-- It's weird. I couldn't make it happen with Twoey b alone: I needed Twoey b + One.

-- I also checked that reordering the arguments made it go away. This...

thygni? : (b : Two) -> Twoey b + One -> ThingyIf b -> Thingy + One
thygni? .ff (tt , ffey) <> = ff , <>
thygni? .tt (tt , ttey) x  = tt , x
thygni? _ _ _ = ff , <>

works : ∀ x → thygni? tt (tt , ttey) x ≡ tt , x
works = λ x → refl

-- Moreover, replacing the gratuitous <> pattern by a variable...

hingy? : (b : Two) -> ThingyIf b -> Twoey b + One -> Thingy + One
hingy? .ff x  (tt , ffey) = ff , <>
hingy? .tt x  (tt , ttey) = tt , x
hingy? _ _ _ = ff , <>

-- ...gives...

works2 : ∀ x → hingy? tt x (tt , ttey) ≡ tt , x
works2 = λ x -> refl

-- ...and it has to be a variable: an _ gives the same outcome as <>.
