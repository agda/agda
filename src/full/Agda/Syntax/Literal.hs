{-# LANGUAGE DeriveDataTypeable #-}
module Agda.Syntax.Literal where

import Data.Generics (Typeable, Data)

import Agda.Syntax.Position

data Literal = LitInt    Range Integer
             | LitLevel  Range Integer
	     | LitFloat  Range Double
	     | LitString Range String
	     | LitChar   Range Char
  deriving (Typeable, Data, Show)

instance Eq Literal where
  LitLevel _ n  == LitLevel _ m  = n == m
  LitInt _ n    == LitInt _ m    = n == m
  LitFloat _ x  == LitFloat _ y  = x == y
  LitString _ s == LitString _ t = s == t
  LitChar _ c   == LitChar _ d   = c == d
  _             == _             = False

instance Ord Literal where
  LitLevel _ n  `compare` LitLevel _ m  = n `compare` m
  LitInt _ n    `compare` LitInt _ m    = n `compare` m
  LitFloat _ x  `compare` LitFloat _ y  = x `compare` y
  LitString _ s `compare` LitString _ t = s `compare` t
  LitChar _ c   `compare` LitChar _ d   = c `compare` d
  compare LitLevel{}    _ = LT
  compare _ LitLevel{} = GT
  compare LitInt{}    _ = LT
  compare _ LitInt{} = GT
  compare LitFloat{}  _ = LT
  compare _ LitFloat{} = GT
  compare LitString{} _ = LT
  compare _ LitString{} = GT

instance HasRange Literal where
  getRange (LitLevel  r _) = r
  getRange (LitInt    r _) = r
  getRange (LitFloat  r _) = r
  getRange (LitString r _) = r
  getRange (LitChar   r _) = r

instance SetRange Literal where
  setRange r (LitLevel  _ x) = LitLevel  r x
  setRange r (LitInt    _ x) = LitInt    r x
  setRange r (LitFloat  _ x) = LitFloat  r x
  setRange r (LitString _ x) = LitString r x
  setRange r (LitChar   _ x) = LitChar   r x

instance KillRange Literal where
  killRange (LitLevel  r x) = LitLevel  (killRange r) x
  killRange (LitInt    r x) = LitInt    (killRange r) x
  killRange (LitFloat  r x) = LitFloat  (killRange r) x
  killRange (LitString r x) = LitString (killRange r) x
  killRange (LitChar   r x) = LitChar   (killRange r) x

