{-# LANGUAGE DeriveDataTypeable #-}

module Agda.Syntax.Literal where

import Control.DeepSeq
import Data.Char
import Data.Typeable (Typeable)
import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name
import Agda.Utils.Pretty
import Agda.Utils.FileName

data Literal = LitNat    Range !Integer
             | LitFloat  Range !Double
             | LitString Range String
             | LitChar   Range !Char
             | LitQName  Range QName
             | LitMeta   Range AbsolutePath MetaId
  deriving (Typeable)

instance Show Literal where
  showsPrec p l = showParen (p > 9) $ case l of
    LitNat _ n    -> sh "LitNat" n
    LitFloat _ x  -> sh "LitFloat" x
    LitString _ s -> sh "LitString" s
    LitChar _ c   -> sh "LitChar" c
    LitQName _ q  -> sh "LitQName" q
    LitMeta _ _ x -> sh "LitMeta" x
    where
      sh :: Show a => String -> a -> ShowS
      sh c x = showString (c ++ " ") . shows x

instance Pretty Literal where
    pretty (LitNat _ n)     = text $ show n
    pretty (LitFloat _ x)   = text $ show x
    pretty (LitString _ s)  = text $ showString' s ""
    pretty (LitChar _ c)    = text $ "'" ++ showChar' c "" ++ "'"
    pretty (LitQName _ x)   = text $ show x
    pretty (LitMeta _ _ x)  = pretty x

showString' :: String -> ShowS
showString' s =
    foldr (.) id $ [ showString "\"" ] ++ map showChar' s ++ [ showString "\"" ]

showChar' :: Char -> ShowS
showChar' '"'   = showString "\\\""
showChar' c
    | escapeMe c = showLitChar c
    | otherwise  = showString [c]
    where
        escapeMe c = not (isPrint c) || c == '\\'

instance Eq Literal where
  LitNat _ n    == LitNat _ m    = n == m
  LitFloat _ x  == LitFloat _ y  = x == y
  LitString _ s == LitString _ t = s == t
  LitChar _ c   == LitChar _ d   = c == d
  LitQName _ x  == LitQName _ y  = x == y
  LitMeta _ f x == LitMeta _ g y = (f, x) == (f, y)
  _             == _             = False

instance Ord Literal where
  LitNat _ n    `compare` LitNat _ m    = n `compare` m
  LitFloat _ x  `compare` LitFloat _ y  = x `compare` y
  LitString _ s `compare` LitString _ t = s `compare` t
  LitChar _ c   `compare` LitChar _ d   = c `compare` d
  LitQName _ x  `compare` LitQName _ y  = x `compare` y
  LitMeta _ f x `compare` LitMeta _ g y = (f, x) `compare` (g, y)
  compare LitNat{}    _ = LT
  compare _ LitNat{}    = GT
  compare LitFloat{}  _ = LT
  compare _ LitFloat{}  = GT
  compare LitString{} _ = LT
  compare _ LitString{} = GT
  compare LitChar{} _   = LT
  compare _ LitChar{}   = GT
  compare LitQName{} _  = LT
  compare _ LitQName{}  = GT
  -- compare LitMeta{} _   = LT
  -- compare _ LitMeta{}   = GT

instance HasRange Literal where
  getRange (LitNat    r _) = r
  getRange (LitFloat  r _) = r
  getRange (LitString r _) = r
  getRange (LitChar   r _) = r
  getRange (LitQName  r _) = r
  getRange (LitMeta r _ _) = r

instance SetRange Literal where
  setRange r (LitNat    _ x) = LitNat    r x
  setRange r (LitFloat  _ x) = LitFloat  r x
  setRange r (LitString _ x) = LitString r x
  setRange r (LitChar   _ x) = LitChar   r x
  setRange r (LitQName  _ x) = LitQName  r x
  setRange r (LitMeta _ f x) = LitMeta   r f x

instance KillRange Literal where
  killRange (LitNat    r x) = LitNat    (killRange r) x
  killRange (LitFloat  r x) = LitFloat  (killRange r) x
  killRange (LitString r x) = LitString (killRange r) x
  killRange (LitChar   r x) = LitChar   (killRange r) x
  killRange (LitQName  r x) = killRange2 LitQName r x
  killRange (LitMeta r f x) = LitMeta   (killRange r) f x

-- | Ranges are not forced.

instance NFData Literal where
  rnf (LitNat _ _)    = ()
  rnf (LitFloat _ _)  = ()
  rnf (LitString _ a) = rnf a
  rnf (LitChar _ _)   = ()
  rnf (LitQName _ a)  = rnf a
  rnf (LitMeta _ _ x) = rnf x
