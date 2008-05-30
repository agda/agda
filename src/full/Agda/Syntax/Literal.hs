{-# OPTIONS -fglasgow-exts #-}

module Agda.Syntax.Literal where

import Data.Generics (Typeable, Data)

import Agda.Syntax.Position

data Literal = LitInt    Range Integer
	     | LitFloat  Range Double
	     | LitString Range String
	     | LitChar   Range Char
    deriving (Typeable, Data, Show)

instance Eq Literal where
    LitInt _ n	    == LitInt _ m	= n == m
    LitFloat _ x    == LitFloat _ y	= x == y
    LitString _ s   == LitString _ t	= s == t
    LitChar _ c	    == LitChar _ d	= c == d
    _		    == _		= False

instance HasRange Literal where
    getRange (LitInt    r _)	= r
    getRange (LitFloat  r _)	= r
    getRange (LitString r _)	= r
    getRange (LitChar   r _)	= r

