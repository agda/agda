{-# LANGUAGE DeriveDataTypeable #-}
module Agda.Syntax.Literal where

import Data.Typeable (Typeable)
import Agda.Syntax.Position
import Agda.Syntax.Abstract.Name

data Literal = LitInt    Range Integer
	     | LitFloat  Range Double
	     | LitString Range String
	     | LitChar   Range Char
             | LitQName  Range QName
  deriving (Typeable)

instance Show Literal where
  showsPrec p l = showParen (p > 9) $ case l of
    LitInt _ n    -> sh "LitInt" n
    LitFloat _ x  -> sh "LitFloat" x
    LitString _ s -> sh "LitString" s
    LitChar _ c   -> sh "LitChar" c
    LitQName _ q  -> sh "LitQName" q
    where
      sh :: Show a => String -> a -> ShowS
      sh c x = showString (c ++ " ") . shows x

instance Eq Literal where
  LitInt _ n    == LitInt _ m    = n == m
  LitFloat _ x  == LitFloat _ y  = x == y
  LitString _ s == LitString _ t = s == t
  LitChar _ c   == LitChar _ d   = c == d
  LitQName _ x  == LitQName _ y  = x == y
  _             == _             = False

instance Ord Literal where
  LitInt _ n    `compare` LitInt _ m    = n `compare` m
  LitFloat _ x  `compare` LitFloat _ y  = x `compare` y
  LitString _ s `compare` LitString _ t = s `compare` t
  LitChar _ c   `compare` LitChar _ d   = c `compare` d
  compare LitInt{}    _ = LT
  compare _ LitInt{} = GT
  compare LitFloat{}  _ = LT
  compare _ LitFloat{} = GT
  compare LitString{} _ = LT
  compare _ LitString{} = GT
  compare LitQName{} _  = LT
  compare _ LitQName{}  = GT

instance HasRange Literal where
  getRange (LitInt    r _) = r
  getRange (LitFloat  r _) = r
  getRange (LitString r _) = r
  getRange (LitChar   r _) = r
  getRange (LitQName  r _) = r

instance SetRange Literal where
  setRange r (LitInt    _ x) = LitInt    r x
  setRange r (LitFloat  _ x) = LitFloat  r x
  setRange r (LitString _ x) = LitString r x
  setRange r (LitChar   _ x) = LitChar   r x
  setRange r (LitQName  _ x) = LitQName  r x

instance KillRange Literal where
  killRange (LitInt    r x) = LitInt    (killRange r) x
  killRange (LitFloat  r x) = LitFloat  (killRange r) x
  killRange (LitString r x) = LitString (killRange r) x
  killRange (LitChar   r x) = LitChar   (killRange r) x
  killRange (LitQName  r x) = LitQName  (killRange r) x
