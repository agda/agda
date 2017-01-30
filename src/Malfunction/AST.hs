module Malfunction.AST where

import Data.Int

data IntType
  = TInt
  | TInt32
  | TInt64
  | TBigint
  deriving (Show, Eq)

data IntConst
  -- I.Int may be the wrong type.
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

{-
type var = Ident.t

let fresh n = Ident.create n

let bind_val e body =
  let v = fresh "x" in
  Mlet ([`Named (v, e)], body (Mvar v))

let bind_rec e body =
  let v = fresh "x" in
  Mlet ([`Recursive [v, e (Mvar v)]], body (Mvar v))

let tuple xs = Mblock(0, xs)

let lambda f =
  let v = fresh "x" in
  Mlambda ([v], f (Mvar v))

let lambda2 f =
  let vx = fresh "x" and vy = fresh "y" in
  Mlambda ([vx; vy], f (Mvar vx) (Mvar vy))

let if_ c tt ff =
  Mswitch (c, [[`Intrange(0,0)], ff; [`Intrange(min_int,max_int);`Deftag], tt])

module IntArith = struct
  let of_int n = Mint (`Int n)
  let zero = of_int 0
  let one = of_int 1
  let (~-) a = Mintop1(`Neg, `Int, a)
  let lnot a = Mintop1(`Not, `Int, a)
  let (+) a b = Mintop2(`Add, `Int, a, b)
  let (-) a b = Mintop2(`Sub, `Int, a, b)
  let ( * ) a b = Mintop2(`Mul, `Int, a, b)
  let (/) a b = Mintop2(`Div, `Int, a, b)
  let (mod) a b = Mintop2(`Mod, `Int, a, b)
  let (land) a b = Mintop2(`And, `Int, a, b)
  let (lor) a b = Mintop2(`Or, `Int, a, b)
  let (lxor) a b = Mintop2(`Xor, `Int, a, b)
  let (lsl) a b = Mintop2(`Lsl, `Int, a, b)
  let (lsr) a b = Mintop2(`Lsr, `Int, a, b)
  let (asr) a b = Mintop2(`Asr, `Int, a, b)
  let (<) a b = Mintop2(`Lt, `Int, a, b)
  let (>) a b = Mintop2(`Gt, `Int, a, b)
  let (<=) a b = Mintop2(`Lte, `Int, a, b)
  let (>=) a b = Mintop2(`Gte, `Int, a, b)
  let (=) a b = Mintop2(`Eq, `Int, a, b)
end

let with_error_reporting ppf def f =
  try f () with
  | Malfunction_sexp.SyntaxError ((locstart, locend), msg) ->
     let open Lexing in
     if locstart.pos_lnum = locend.pos_lnum then
       Format.fprintf ppf "%s:%d:%d-%d: %s\n%!"
         locstart.pos_fname locstart.pos_lnum (locstart.pos_cnum - locstart.pos_bol) (locend.pos_cnum - locend.pos_bol) msg
     else
       Format.fprintf ppf "%s:%d:%d-%d:%d %s\n%!"
         locstart.pos_fname locstart.pos_lnum (locstart.pos_cnum - locstart.pos_bol) locend.pos_lnum (locend.pos_cnum - locend.pos_bol) msg;
     def
  | x ->
     Location.report_exception ppf x;
    def

-}
