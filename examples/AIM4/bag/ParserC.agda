
module ParserC where

{-

  import Prelude
  import Equiv
  import Eq
  import Datoid
  import List
  import Bag

  open Prelude
  open Equiv
  open Eq
  open Datoid
  open List
  open Bag

  parserDatoid : (a, s : Datoid) -> Datoid
  parserDatoid a s = Bag (pairDatoid a (listDatoid s))

-- We use the following datatype instead of
--   type Parsing s a = [s] -> Bag (a, [s])
  data Parsing (s, a : Datoid) : Set1 where
    P :  (List (El s) -> El (parserDatoid a s)) -> Parsing s a

  private
    unP :  {s, a : Datoid} -> Parsing s a
        -> List (El s) -> El (parserDatoid a s)
    unP (P x) = x

    _<+>_ :  {a : Datoid} -> El (Bag a) -> El (Bag a) -> El (Bag a)
    _<+>_ {a} x y = bagElim (\bs -> El (Bag a)) ? y (\z zs ih -> insert z ih) x

    concatMap :  {a, b : Datoid} -> (El a -> El (Bag b)) -> El (Bag a)
              -> El (Bag b)
    concatMap {a} {b} f = bagElim (\bs -> El (Bag b)) ? empty (\x b ih -> f x <+> ih)

  symbol : {s : Datoid} -> Parsing s s
  symbol {s} = P symbol'
    where
    symbol' : List (El s) -> El (parserDatoid s s)
    symbol' nil       = empty
    symbol' (x :: xs) = insert (pair x xs) empty


  fail : {s, a : Datoid} -> Parsing s a
  fail = P (\ss -> empty)

  (+++) : {s, a : Datoid} -> Parsing s a -> Parsing s a -> Parsing s a
  P p +++ P q = P (\s -> p s <+> q s)

  return :  {s, a : Datoid} -> (x : El a) -> Parsing s a
  return = \x -> P (\s -> insert (pair x s) empty)

--  data Traverse (a : Datoid) : Set where
--    Empty  : Traverse a
--    Insert : (x : El a) -> (b : El (Bag a)) -> Traverse a

--  run : {a : Datoid} -> Traverse a -> El (Bag a)
--  traverse : {a : Datoid} -> El (Bag a) -> Traverse a
--  traverseTraverses
--    :  {a : Datoid} -> (b : El (Bag a)) -> run (traverse b) =^= b

-- insert : {a : Datoid} -> El a -> El (Bag a) -> El (Bag a)
-- pairDatoid : Datoid -> Datoid -> Datoid
--(empty {Bag (pairDatoid s (listDatoid s))})
--  bagElim
--    :  {a : Datoid}
--    -> (P : El (Bag a) -> Set)
--    -> P empty
--    -> ((x : El a) -> (b : El (Bag a)) -> P b -> P (insert x b))
--    -> (b : El (Bag a))
--    -> P b


  (>>=) : {s, a, b : Datoid}
        -> Parsing s a -> (El a -> Parsing s b) -> Parsing s b
  (>>=) {s} {a} {b} (P p) k
        = P (\s -> concatMap (\y -> unP (k (fst y)) (snd y)) (p s))

{-
  parserDatoid : (a, s : Datoid) -> Datoid
  parserDatoid a s = Bag (pairDatoid a (listDatoid s))

-- We use the following datatype instead of
--   type Parsing s a = [s] -> Bag (a, [s])
  data Parsing (s, a : Datoid) : Set1 where
    P :  (List (El s) -> El (parserDatoid a s))
      -> Parsing s a

-}

-}
