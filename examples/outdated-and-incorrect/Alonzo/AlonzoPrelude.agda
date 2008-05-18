module AlonzoPrelude where
  open import RTN public
  import RTP  -- magic module - Run Time Primitives
  
  Int : Set
  Int = RTP.Int

  Float : Set
  Float = RTP.Float

  String : Set
  String = RTP.String 

  Char : Set
  Char = RTP.Char


  data True : Set where
    tt : True

{-
  record True : Set where

  tt : True
  tt = record{}
-}
  data False : Set where

  elim-False : {A : Set} -> False -> A
  elim-False ()

  
  -- _∘_ : {A,B,C:Set} -> (B -> C) -> (A -> B) -> A -> C
  -- f ∘ g = \x -> f (g x)

  id : {A : Set} -> A -> A
  id x = x

  infixr 90 _○_
  _○_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
  (f ○ g) x = f (g x)

  infixr 0 _$_
  _$_ : {A B : Set} -> (A -> B) -> A -> B
  f $ x = f x

  flip : {A B C : Set} -> (A -> B -> C) -> B -> A -> C
  flip f x y = f y x

  const : {A B : Set} -> A -> B -> A
  const x _ = x

  typeOf : {A : Set} -> A -> Set
  typeOf {A} _ = A

  data _×_ (A B : Set) : Set where
    <_,_> : A -> B -> A × B

  fst : {A B : Set} -> A × B -> A
  fst < x , y > = x

  snd : {A B : Set} -> A × B -> B
  snd < x , y > = y

{-
  infixr 10 _::_
  data List (A:Set) : Set where
    nil  : List A
    _::_ : A -> List A -> List A

 
  [_] : {A:Set} -> A -> List A
  [ x ] = x :: nil
-}
  {-# BUILTIN INTEGER Int    #-}
--  {-# BUILTIN STRING  String #-}
--   {-# BUILTIN FLOAT   Float  #-}
  {-# BUILTIN CHAR    Char   #-}
  
