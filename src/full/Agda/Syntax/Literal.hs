
module Agda.Syntax.Literal where

import Control.DeepSeq
import Data.Char
import Data.Word

import Data.Text (Text)
import qualified Data.Text as T

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name
import Agda.Utils.FileName
import Agda.Utils.Float ( doubleDenotEq, doubleDenotOrd )
import Agda.Utils.Pretty

type RLiteral = Ranged Literal
data Literal
  = LitNat    !Integer
  | LitWord64 !Word64
  | LitFloat  !Double
  | LitString !Text
  | LitChar   !Char
  | LitQName  !QName
  | LitMeta   AbsolutePath MetaId
  deriving Show

instance Pretty Literal where
    pretty (LitNat n)     = pretty n
    pretty (LitWord64 n)  = pretty n
    pretty (LitFloat d)   = pretty d
    pretty (LitString s)  = text $ showText s ""
    pretty (LitChar c)    = text $ "'" ++ showChar' c "'"
    pretty (LitQName x)   = pretty x
    pretty (LitMeta _ x)  = pretty x

showText :: Text -> ShowS
showText s = showString "\""
           . T.foldr (\ c -> (showChar' c .)) id s
           . showString "\""

showChar' :: Char -> ShowS
showChar' '"'   = showString "\\\""
showChar' c
    | escapeMe c = showLitChar c
    | otherwise  = showString [c]
    where
        escapeMe c = not (isPrint c) || c == '\\'

instance Eq Literal where
  LitNat n    == LitNat m    = n == m
  -- ASR (2016-09-29). We use bitwise equality for comparing Double
  -- because Haskell's Eq, which equates 0.0 and -0.0, allows to prove
  -- a contradiction (see Issue #2169).
  LitWord64 n == LitWord64 m = n == m
  LitFloat x  == LitFloat y  = doubleDenotEq x y
  LitString s == LitString t = s == t
  LitChar c   == LitChar d   = c == d
  LitQName x  == LitQName y  = x == y
  LitMeta f x == LitMeta g y = (f, x) == (g, y)
  _           == _             = False

instance Ord Literal where
  LitNat n    `compare` LitNat m    = n `compare` m
  LitWord64 n `compare` LitWord64 m = n `compare` m
  LitFloat x  `compare` LitFloat y  = doubleDenotOrd x y
  LitString s `compare` LitString t = s `compare` t
  LitChar c   `compare` LitChar d   = c `compare` d
  LitQName x  `compare` LitQName y  = x `compare` y
  LitMeta f x `compare` LitMeta g y = (f, x) `compare` (g, y)
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

instance KillRange Literal where
  killRange (LitNat    x) = LitNat    x
  killRange (LitWord64 x) = LitWord64 x
  killRange (LitFloat  x) = LitFloat  x
  killRange (LitString x) = LitString x
  killRange (LitChar   x) = LitChar   x
  killRange (LitQName  x) = killRange1 LitQName x
  killRange (LitMeta f x) = LitMeta f x

-- | Ranges are not forced.

instance NFData Literal where
  rnf (LitNat _     ) = ()
  rnf (LitWord64 _  ) = ()
  rnf (LitFloat _   ) = ()
  rnf (LitString _  ) = ()
  rnf (LitChar _    ) = ()
  rnf (LitQName a   ) = rnf a
  rnf (LitMeta _ x  ) = rnf x
