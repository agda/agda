{-# LANGUAGE DeriveDataTypeable #-}
module Agda.Syntax.Literal where

import Data.Generics (Typeable, Data)

import Agda.Syntax.Position

data Literal = LitInt    Range Integer
	     | LitFloat  Range Double
	     | LitString Range String
	     | LitChar   Range Char
  deriving (Typeable, Data, Show)

instance Eq Literal where
  LitInt _ n    == LitInt _ m    = n == m
  LitFloat _ x  == LitFloat _ y  = x == y
  LitString _ s == LitString _ t = s == t
  LitChar _ c   == LitChar _ d   = c == d
  _             == _             = False

instance HasRange Literal where
  getRange (LitInt    r _)	= r
  getRange (LitFloat  r _)	= r
  getRange (LitString r _)	= r
  getRange (LitChar   r _)	= r

instance SetRange Literal where
  setRange r (LitInt    _ x)	= LitInt    r x
  setRange r (LitFloat  _ x)	= LitFloat  r x
  setRange r (LitString _ x)	= LitString r x
  setRange r (LitChar   _ x)	= LitChar   r x

instance KillRange Literal where
  killRange (LitInt    r x) = LitInt    (killRange r) x
  killRange (LitFloat  r x) = LitFloat  (killRange r) x
  killRange (LitString r x) = LitString (killRange r) x
  killRange (LitChar   r x) = LitChar   (killRange r) x

