module Malfunction.AST
  ( IntType(..)
  , IntConst(..)
  , UnaryIntOp(..)
  , BinaryIntOp(..)
  , VectorType(..)
  , Mutability(..)
  , BlockTag
  , Case(..)
  , Ident
  , Longident
  , Mod(..)
  , Term(..)
  , Binding(..)
  -- NOTE: I don't know which of these is preferable
  --  * Don't re-export anything from Agda.Utils.Pretty
  --  * export a few things (like we do currently)
  --  * Re-export the whole module
  , pretty
  , prettyShow
  ) where

import Data.Int
import Text.Printf
-- Bafflingly there is no type-class for pretty-printable-stuff
-- in `Text.Printf` -- so we'll use the definition in agda.
import Agda.Utils.Pretty

data IntType
  = TInt
  | TInt32
  | TInt64
  | TBigint
  deriving (Show, Eq)

data IntConst
  -- Int may be the wrong type.
  --
  -- In malfunction Int is:
  --
  -- > `int` uses either 31- or 63- bit two's complement arithmetic
  -- > (depending on system word size, and also wrapping on overflow)
  -- > https://github.com/stedolan/malfunction/blob/master/docs/spec.md
  --
  -- And in Haskell:
  -- > A fixed-precision integer type with at least the range
  -- > [-2^29 .. 2^29-1]
  -- > https://hackage.haskell.org/package/base-4.9.0.0/docs/Data-Int.html
  --
  -- Jan: Just run
  -- logBase 2 ((fromIntegral (maxBound :: Int)) :: Double)
  -- in my computer (64 bits) --> 2 ^ 63 - 1 == (maxBound :: Int)
  = CInt Int
  | CInt32 Int32
  | CInt64 Int64
  | CBigint Integer
  deriving (Show, Eq)

data UnaryIntOp = Neg | Not
  deriving (Show, Eq)

data BinaryIntOp
  = Add | Sub | Mul | Div | Mo | And | Or | Xor | Lsl | Lsr | Asr
  | Lt | Gt | Lte | Gte | Eq
  deriving (Show, Eq)

data VectorType = Array | Bytevec
  deriving (Show, Eq)

data Mutability = Inm | Mut
  deriving (Show, Eq)

type BlockTag = Int

-- The spec and the ocaml implementation are inconsistent when defining Case.
-- I'll use the definition (examples) from the spec to guide this implementation.
-- I know I could've used Maybe's here, but not doing so was a concious choice.
--
-- Any tag value above 200 is an error in malfunction.
data Case
  -- (tag _)
  = Deftag
  -- (tag n)
  | Tag Int
  -- _
  | CaseAnyInt
  -- n
  | CaseInt Int
  -- (n m)
  | Intrange (Int, Int)
  deriving (Show, Eq)

maxTag :: Integer
maxTag = 200
tagOfInt :: Integer -> Integer
tagOfInt n =
  if 0 <= n && n < maxTag
  then n
  else error "tag out of range"

-- `Term` references OCaml modules `Ident` and `Longident`
-- TODO: Bindings for modules Ident and Longident
type Ident = String

type Longident = [Ident]
--data Longident
--  = Lident String
--  | Ldot   Longident String
--  | Lapply Longident Longident

-- "The top-level sexp must begin with the atom module, followed by a
-- list of bindings (described under let, below), followed by an sexp
-- beginning with the atom export."
data Mod = MMod [Binding] [Term]

data Term
  = Mvar Ident
  | Mlambda [Ident] Term
  | Mapply Term [Term]
  | Mlet [Binding] Term
  | Mint IntConst
  | Mstring String
  | Mglobal Longident
  | Mswitch Term [([Case], Term)]
  -- Integers
  | Mintop1 UnaryIntOp IntType Term
  | Mintop2 BinaryIntOp IntType Term Term
  | Mconvert IntType IntType Term
  -- Vectors
  | Mvecnew VectorType Term Term
  | Mvecget VectorType Term Term
  | Mvecset VectorType Term Term Term
  | Mveclen VectorType Term
  -- Blocks
  | Mblock Int [Term]
  | Mfield Int Term
  deriving (Show, Eq)


data Binding
  -- "(_ EXP)"
  = Unnamed Term
  -- "($var EXP)"
  | Named Ident Term
  -- "(rec ($VAR1 EXP1) ($VAR2 EXP2) ...)"
  | Recursive [(Ident, Term)]
  deriving (Show, Eq)

instance Pretty Mod where
  pretty = text . showMod

showMod :: Mod -> String
showMod (MMod bs ts) = printf "(module %s (export %s))"
  (unwords . map showBinding $ bs)
  (unwords . map showTerm $ ts)

instance Pretty Term where
  pretty = text . showTerm

showTerm :: Term -> String
showTerm tt = case tt of
  Mvar i              -> showIdent i
  Mlambda is t        -> printf "(lambda (%s) %s)" (unwords (map showIdent is)) (showTerm t)
  Mapply t ts         -> printf "(apply %s %s)" (showTerm t) (unwords . map showTerm $ ts)
  Mlet bs t           -> printf "(let %s %s)" (unwords (map showBinding bs)) (showTerm t)
  Mint ic             -> printf "%s" (showIntConst ic)
  Mstring s           -> printf "%s" (show s)
  Mglobal li          -> printf "(global %s)" (showLongident li)
  Mswitch t cexps     -> printf "(switch %s %s)" (showTerm t) (unwords (map showCaseExpression cexps))
 -- Integers
  Mintop1 op tp t0    -> printf "(%s %s)" (showUnaryIntOp op) (showTypedTerm tp t0)
  Mintop2 op tp t0 t1 -> printf "(%s %s %s)" (showBinaryIntOp op) (showTypedTerm tp t0) (showTypedTerm tp t1)
  Mconvert tp0 tp1 t0 -> printf "(convert.%s.%s %s)" (showIntType tp0) (showIntType tp1) (showTerm t0)
  -- Vectors
  Mvecnew tp t0 t1    -> printf "(makevec %s %s)"  (showTerm t0) (showTerm t1)
  Mvecget tp t0 t1    -> printf "(load %s %s)"     (showTerm t0) (showTerm t1)
  Mvecset tp t0 t1 t2 -> printf "(store %s %s %s)" (showTerm t0) (showTerm t1) (showTerm t2)
  Mveclen tp t0       -> printf "(length %s)"      (showTerm t0)
  -- Blocks
  Mblock i ts         -> printf "(block (tag %s) %s)" (show i) (unwords (map showTerm ts))
  Mfield i t0         -> printf "(field %s %s)" (show i) (showTerm t0)

instance Pretty Binding where
  pretty = text . showBinding

showBinding :: Binding -> String
showBinding b = case b of
  Unnamed t    -> printf "(_ %s)" (showTerm t)
  Named i t    -> printf "(%s %s)" (showIdent i) (showTerm t)
  Recursive bs -> printf "(rec %s)" (unwords (map showIdentTerm bs))
  where
    showIdentTerm :: (Ident, Term) -> String
    showIdentTerm (i, t) = printf "(%s %s)" (showIdent i) (showTerm t)

instance Pretty IntConst where
  pretty = text . showIntConst

showIntConst :: IntConst -> String
showIntConst ic = case ic of
  CInt    i -> show i
  CInt32  i -> show i
  CInt64  i -> show i
  CBigint i -> show i

-- Problematic:
-- instance Pretty Longident where
--   pretty = text . showLongident

showLongident :: Longident -> String
showLongident = unwords . map showIdent

-- Ditto problematic:
-- instance Pretty Ident where
--   pretty = text . showIdent

showIdent :: Ident -> String
showIdent = ('$':)

-- Ditto problematic:
-- instance Pretty ([Case], Term) where
--   pretty = text . showCaseExpression

showCaseExpression :: ([Case], Term) -> String
showCaseExpression (cs, t) = printf "(%s %s)" (unwords (map showCase cs)) (showTerm t)

instance Pretty Case where
  pretty = text . showCase

-- I don't think it's possible to create `_` and `n` as mentioned in the spec
-- using the AST define in the original implementation of malfunction.
showCase :: Case -> String
showCase c = case c of
  Deftag          -> "(tag _)"
  Tag n           -> printf "(tag %s)" (show n)
  CaseAnyInt      -> "_"
  CaseInt n       -> show n
  Intrange (i, j) -> printf "(%s %s)" (show i) (show j)

instance Pretty UnaryIntOp where
  pretty = text . showUnaryIntOp

showUnaryIntOp :: UnaryIntOp -> String
showUnaryIntOp op = case op of
  Neg -> "?"
  Not -> "?"

instance Pretty BinaryIntOp where
  pretty = text . showBinaryIntOp

showBinaryIntOp :: BinaryIntOp -> String
showBinaryIntOp op = case op of
  Add -> "+"
  Sub -> "-"
  Mul -> "*"
  Div -> "/"
  Mo  -> "%"
  And -> "&"
  Or  -> "|"
  Xor -> "^"
  Lsl -> "<<"
  Lsr -> ">>"
  Asr  -> "a>>"
  Lt  -> "<"
  Gt  -> ">"
  Lte -> "<="
  Gte -> ">="
  Eq  -> "=="

-- Problematic:

showTypedTerm :: IntType -> Term -> String
showTypedTerm tp t = case tp of
  TInt -> showTerm t
  _    -> printf "%s.%s" (showTerm t) (showIntType tp)

instance Pretty IntType where
  pretty = text . showIntType

showIntType :: IntType -> String
showIntType tp = case tp of
  TInt    -> "int"
  TInt32  -> "int32"
  TInt64  -> "int64"
  TBigint -> "bigint"
