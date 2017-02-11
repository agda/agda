{-# LANGUAGE OverloadedStrings #-}
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
-- There does exist a definition of a type-class `Pretty` in the package
-- `pretty` but this is not the one used for Treeless terms, so for consistency,
-- let's go with Agda's choice.
import Agda.Utils.Pretty
import Text.PrettyPrint

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
-- TODO: I would maybe like to stay clear of type-synonyms in this
-- module altogether.
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

-- Pretty-printing functionality
-- TODO: There is one issue with the current implementation:
-- Consider this example:
--
--     ($12.8247419466833350538 (lambda ($v0)
--                                 (switch $v0 ((tag 0) (let ($v1 (field 0 $v0)) $v1)))))
--
-- What we see here is that when `nest` is invoked after the parameters of the
-- lambda-expression the nesting references the beginning of the
-- lambda-expression. Ideally it should reference the beggining of that line.
-- Also, brackets should be closed in the same column that they are opened. So
-- the above example would become:
--
--     ($12.8247419466833350538
--       (lambda ($v0)
--         (switch $v0 ((tag 0) (let ($v1 (field 0 $v0)) $v1)))
--       )
--     )
--
-- Also, it would be nice to have a way of deferring line-skips in case the stuff
-- we're printing fits within some limit (say 70 characters). So that we won't print
-- stuff like:
--
--     ( apply
--       $f
--       0
--       1
--     )

textShow :: Show a => a -> Doc
textShow = text . show

nst :: Doc -> Doc
nst = nest 2

(<.>) :: Doc -> Doc -> Doc
a <.> b = a <> "." <> b

level :: Doc -> Doc -> Doc
level a b = vcat [ "(" <+> a, nst b, ")" ]

instance Pretty Mod where
--   pretty (MMod bs ts) = "(module " $$ nst (vcat (map pretty bs)) $$ "(export" <+> prettyList ts <+> "))"
  pretty (MMod bs ts) = vcat ["module", nest 2 (vcat (map pretty bs ++ [parens ("export" <+> prettyList ts)]))]
  prettyPrec _ = pretty

instance Pretty Term where
  pretty tt = case tt of
    Mvar i              -> prettyIdent i
    Mlambda is t        -> level ("lambda" <+> parens (hsep (map prettyIdent is))) (pretty t)
    Mapply t ts         -> level ("apply " <> pretty t) (vcat . map pretty $ ts)
    Mlet bs t           -> level "let" (prettyList bs $$ pretty t)
    Mint ic             -> pretty ic
    Mstring s           -> textShow s
    Mglobal li          -> parens $ "global" <+> prettyLongident li
    Mswitch t cexps     -> level ("switch" <+> pretty t) (vcat (map prettyCaseExpression cexps))
    -- Integers
    Mintop1 op tp t0    -> pretty op <+> prettyTypedTerm tp t0
    Mintop2 op tp t0 t1 -> level (pretty op) (vcat [prettyTypedTerm tp t0, prettyTypedTerm tp t1])
    Mconvert tp0 tp1 t0 -> parens $ "convert" <.> pretty tp0 <.> pretty tp1 <+> pretty t0
    -- Vectors
    Mvecnew tp t0 t1    -> level "makevec" (vcat [pretty t0, pretty t1])
    Mvecget tp t0 t1    -> level "load" (vcat [pretty t0, pretty t1])
    Mvecset tp t0 t1 t2 -> level "store" (vcat [pretty t0, pretty t1, pretty t2])
    Mveclen tp t0       -> level "length" (pretty t0)
    -- Blocks
    Mblock i ts         -> level ("block" <+> parens ("tag" <+> pretty i)) (prettyList ts)
    Mfield i t0         -> parens $ "field" <+> pretty i <+> pretty t0
  prettyPrec _ = pretty

instance Pretty Binding where
  pretty b = case b of
    Unnamed t    -> level "_" (pretty t)
    Named i t    -> level (prettyIdent i) (pretty t)
    Recursive bs -> level "rec" (vcat (map showIdentTerm bs))
    where
      showIdentTerm :: (Ident, Term) -> Doc
      showIdentTerm (i, t) = level (pretty i) (pretty t)

instance Pretty IntConst where
  pretty ic = case ic of
    CInt    i -> pretty i
    CInt32  i -> pretty i
    CInt64  i -> textShow i
    CBigint i -> pretty i

-- Problematic:
-- instance Pretty Longident where
--   pretty = text . showLongident

prettyLongident :: Longident -> Doc
prettyLongident = hcat . map prettyIdent

-- Ditto problematic:
-- instance Pretty Ident where
--   pretty = text . showIdent

prettyIdent :: Ident -> Doc
prettyIdent = text . ('$':)

-- Ditto problematic:
-- instance Pretty ([Case], Term) where
--   pretty = text . showCaseExpression

prettyCaseExpression :: ([Case], Term) -> Doc
prettyCaseExpression (cs, t) = level (prettyList cs) (pretty t)

instance Pretty Case where
  pretty c = case c of
    Deftag          -> "(tag _)"
    Tag n           -> "(tag " <> pretty n <> ")"
    CaseAnyInt      -> "_"
    CaseInt n       -> pretty n
    Intrange (i, j) -> "(" <> pretty i <+> pretty j <> ")"

instance Pretty UnaryIntOp where
  pretty op = case op of
    Neg -> "?"
    Not -> "?"

instance Pretty BinaryIntOp where
  pretty op = case op of
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

prettyTypedTerm :: IntType -> Term -> Doc
prettyTypedTerm tp t = case tp of
  TInt -> pretty t
  _    -> pretty t <.> pretty tp

instance Pretty IntType where
  pretty tp = case tp of
    TInt    -> "int"
    TInt32  -> "int32"
    TInt64  -> "int64"
    TBigint -> "bigint"
