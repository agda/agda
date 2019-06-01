{-# LANGUAGE DeriveDataTypeable #-}

module Agda.Syntax.Literal where

import Control.DeepSeq
import Data.Char
import Data.Word

import Data.Data (Data)

import Numeric.IEEE ( IEEE(identicalIEEE) )

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name
import Agda.Utils.Pretty
import Agda.Utils.FileName

data Literal = LitNat    Range !Integer
             | LitWord64 Range !Word64
             | LitFloat  Range !Double
             | LitString Range String
             | LitChar   Range !Char
             | LitQName  Range QName
             | LitMeta   Range AbsolutePath MetaId
  deriving Data

instance Show Literal where
  showsPrec p l = showParen (p > 9) $ case l of
    LitNat _ n    -> sh "LitNat _" n
    LitWord64 _ n -> sh "LitWord64 _" n
    LitFloat _ x  -> sh "LitFloat _" x
    LitString _ s -> sh "LitString _" s
    LitChar _ c   -> sh "LitChar _" c
    LitQName _ q  -> sh "LitQName _" q
    LitMeta _ _ x -> sh "LitMeta _ _" x
    where
      sh :: Show a => String -> a -> ShowS
      sh c x = showString (c ++ " ") . shows x

instance Pretty Literal where
    pretty (LitNat _ n)     = text $ show n
    pretty (LitWord64 _ n)  = text $ show n
    pretty (LitFloat _ d)   = text $ show d
    pretty (LitString _ s)  = text $ showString' s ""
    pretty (LitChar _ c)    = text $ "'" ++ showChar' c "'"
    pretty (LitQName _ x)   = pretty x
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
  -- ASR (2016-09-29). We use bitwise equality for comparing Double
  -- because Haskell's Eq, which equates 0.0 and -0.0, allows to prove
  -- a contradiction (see Issue #2169).
  LitWord64 _ n == LitWord64 _ m = n == m
  LitFloat _ x  == LitFloat _ y  = identicalIEEE x y || (isNaN x && isNaN y)
  LitString _ s == LitString _ t = s == t
  LitChar _ c   == LitChar _ d   = c == d
  LitQName _ x  == LitQName _ y  = x == y
  LitMeta _ f x == LitMeta _ g y = (f, x) == (f, y)
  _             == _             = False

instance Ord Literal where
  LitNat _ n    `compare` LitNat _ m    = n `compare` m
  LitWord64 _ n `compare` LitWord64 _ m = n `compare` m
  LitFloat _ x  `compare` LitFloat _ y  = compareFloat x y
  LitString _ s `compare` LitString _ t = s `compare` t
  LitChar _ c   `compare` LitChar _ d   = c `compare` d
  LitQName _ x  `compare` LitQName _ y  = x `compare` y
  LitMeta _ f x `compare` LitMeta _ g y = (f, x) `compare` (g, y)
  compare LitNat{}    _ = LT
  compare _ LitNat{}    = GT
  compare LitWord64{} _ = LT
  compare _ LitWord64{} = GT
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

-- NOTE: This is not the same ordering as primFloatNumericalEquality!
-- This ordering must be a total order of all allowed float values,
-- while primFloatNumericalEquality is only a preorder
compareFloat :: Double -> Double -> Ordering
compareFloat x y
  | identicalIEEE x y          = EQ
  | isNegInf x                 = LT
  | isNegInf y                 = GT
  | isNaN x && isNaN y         = EQ
  | isNaN x                    = LT
  | isNaN y                    = GT
  | isNegativeZero x && x == y = LT
  | isNegativeZero y && x == y = GT
  | otherwise                  = compare x y
  where
    isNegInf z = z < 0 && isInfinite z

instance HasRange Literal where
  getRange (LitNat    r _) = r
  getRange (LitWord64 r _) = r
  getRange (LitFloat  r _) = r
  getRange (LitString r _) = r
  getRange (LitChar   r _) = r
  getRange (LitQName  r _) = r
  getRange (LitMeta r _ _) = r

instance SetRange Literal where
  setRange r (LitNat    _ x) = LitNat    r x
  setRange r (LitWord64 _ x) = LitWord64 r x
  setRange r (LitFloat  _ x) = LitFloat  r x
  setRange r (LitString _ x) = LitString r x
  setRange r (LitChar   _ x) = LitChar   r x
  setRange r (LitQName  _ x) = LitQName  r x
  setRange r (LitMeta _ f x) = LitMeta   r f x

instance KillRange Literal where
  killRange (LitNat    r x) = LitNat    (killRange r) x
  killRange (LitWord64 r x) = LitWord64 (killRange r) x
  killRange (LitFloat  r x) = LitFloat  (killRange r) x
  killRange (LitString r x) = LitString (killRange r) x
  killRange (LitChar   r x) = LitChar   (killRange r) x
  killRange (LitQName  r x) = killRange2 LitQName r x
  killRange (LitMeta r f x) = LitMeta   (killRange r) f x

-- | Ranges are not forced.

instance NFData Literal where
  rnf (LitNat _ _)    = ()
  rnf (LitWord64 _ _) = ()
  rnf (LitFloat _ _)  = ()
  rnf (LitString _ a) = rnf a
  rnf (LitChar _ _)   = ()
  rnf (LitQName _ a)  = rnf a
  rnf (LitMeta _ _ x) = rnf x
