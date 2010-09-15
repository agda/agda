module Issue276 where

boo : {S T : Set}(f : S -> T)(x y : S) ->
      ((P : S -> Set) -> P x -> P y) ->
       (P : T -> Set) -> P (f x) -> P (f y)
boo = \ f x y q P -> q (\ s -> P (f s))

record Pack (S : Set) : Set where
  constructor pack
  field
    unpack : S

open Pack

unpack' : {S : Set} -> Pack S -> S
unpack' (pack s) = s

foo : {S : Set}(x : Pack S)(P : Pack S -> Set) -> P (pack (unpack x)) -> P x
foo = \ x P p -> p

goo : {S : Set}(x : Pack S)(P : S -> Set) -> P (unpack x) -> P (unpack' x)
goo = \ x -> boo unpack' (pack (unpack x)) x (foo x)

{- normal form of goo is \ x P p -> p -}

goo' : {S : Set}(x : Pack S)(P : S -> Set) -> P (unpack x) -> P (unpack' x)
goo' = \ x P p -> p
{-
/Users/conor/Desktop/fooling/RecConBug.agda:27,19-20
unpack x != unpack' x of type .S
when checking that the expression p has type P (unpack' x)
-}
