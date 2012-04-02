module MixFix2 (main) where

import Control.Monad
import Data.List
import Data.Char
import System.Environment

import Utils.ReadP
import Utils.TestHelpers
import Utils.IO
import Prelude hiding (putStrLn, print)

------------------------------------------------------------------------
-- Parser combinators

-- @'intersperseP' inside ts@ parses the tokens @ts@, separated by
-- @inside@. The values returned by the @inside@ parser are returned.

intersperseP :: Eq token => ReadP token a -> [token] -> ReadP token [a]
intersperseP inside ts =
  liftM rights $
  sequence $
  intersperse (liftM Right inside)
              (map (liftM Left . char) ts)
  where
  rights []             = []
  rights (Right x : xs) = x : rights xs
  rights (Left _  : xs) = rights xs

-- Associativity.

data Assoc
  = Lft   -- ^ Left associative.
  | Rght  -- ^ Right associative.
  | Non   -- ^ Nonassociative.
    deriving (Show, Eq)

-- Operator descriptions. Note that the inner parts of mixfix
-- operators are not included in these descriptions.

data Op a
  = Bin  (a -> a -> a) Assoc
    -- ^ Binary operator with a function constructing an application
    -- from the left and right arguments, and the associativity of the
    -- operator.
  | Pre  (a -> a)
    -- ^ Prefix operator.
  | Post (a -> a)
    -- ^ Postfix operator.

-- | Checks that the input, a sequence of terms (left) or operators
-- (right), is valid. If it is valid the result of applying the
-- operators to the terms is computed.
--
-- The sequence has to satisfy these properties:
--
-- * First zero or more postfix applications.
--
-- * Then either
--
--   * zero or one nonassociative infix applications,
--
--   * zero or more left associative infix applications, or
--
--   * zero or more right associative infix applications.
--
-- * And finally zero or more prefix applications.
--
-- * With the exception that there may not be both prefix and postfix
--   applications if there are zero infix applications.
--
-- As an example, assume that @-@ is prefix, @+@, @*@ and @/@ infix,
-- and @!@ postfix, all of the same precedence, with @+@ left
-- associative, @*@ right associative, and @/@ nonassociative. All
-- nonambiguous parses are OK, so
--   @- - 3@, @4 ! !@, @5 * - 3@, @5 ! + 2 + 3@ and @2 / - - 3@
-- are OK, whereas
--   @- 3 !@, @- 3 * 5@, @5 + 2 + ! 3@ and @2 / 3 / 4@
-- are not.

checkOpApps :: ReadP (Either a (Op a)) a
checkOpApps = atLeastOneMid +++ pres many1 +++ posts many
  where
  elem = do
    Left x <- get
    return x

  ass Non = mzero
  ass a   = do
    Right (Bin o a') <- get
    guard (a == a')
    return o

  pres c = do
    ps <- c (do Right (Pre o) <- get; return o)
    e  <- elem
    return $ foldr ($) e ps

  posts c = do
    e  <- elem
    ps <- c (do Right (Post o) <- get; return o)
    return $ foldr ($) e ps

  atLeastOneMid = do
    e1 <- posts many
    Right (Bin o a) <- get
    eos <- many (liftM2 (,) elem (ass a))
    e2 <- pres many
    return $ case a of
      Lft -> let (es, os) = unzip eos
                 eos'     = zip (es ++ [e2]) (o : os)
             in  foldl (\l (r, o) -> l `o` r) e1 eos'
      _   -> foldr (\(l, o) r -> l `o` r) e2 ((e1, o) : eos)

-- Parses zero or more operator applications.

op :: Eq token
   => [([token], [a] -> Op a)]
      -- ^ Describes a bunch of operators with varying associativity
      -- but equal precedence. The first component of every pair lists
      -- the tokens building up the operator; if there are several
      -- tokens, then the operator is mixfix. The second component
      -- creates an operator description, given the contents for the
      -- "middle" parts of the operator (an empty list in the case of
      -- non-mixfix operators).
   -> ReadP token a
      -- ^ Parser for the terms between the operators.
   -> ReadP token a
      -- ^ Parser for the terms inside mixfix operators.
   -> ReadP token a
op table rest inside = do
  opApps <- many1 (liftM Left rest +++ liftM Right p)
  case parse checkOpApps opApps of
    [e] -> return e
    _   -> mzero
  where
  p = choice $ map (\(ts, o) -> liftM o $ intersperseP inside ts)
                   table

------------------------------------------------------------------------
-- Example parser

-- expr is a parser for the following fixity declarations, plus
-- variables, parentheses and the nonfix operator ⟦_,_⟧:
--
-- infixl _+_ _-_
-- infix  -_      binds tighter-than (_+_)
-- infixl _*_ _/_ binds tighter-than (_+_) looser-than (-_)
--
-- infixr _∧_
-- infix  !_      binds tighter-than (_∧_)
-- infixr _∨_ _⊕_ binds looser-than (_∧_)
-- infixl _⇐_     binds looser-than (_∧_)
-- infixr _⇒_     binds as _⇐_
-- infix  I_T_E_  binds as _⇒_
--
-- infix  _≡_     binds looser-than (_+_ _⊕_ _⇒_)
-- infix  ¬_      binds looser-than (_≡_)
-- infix  _?      binds tighter-than (_≡_)
--
-- infixr _,_     binds tighter-than (_-_ !_)

data BinOp = Plus | Minus | Mul | Div | And | Or | Xor | Eq
           | Impl | RevImpl | Pair | Sem
             deriving (Show, Eq)
data UnOp  = Neg | BoolNot | Not | Quest
             deriving (Show, Eq)

data Expr
  = IfThenElse Expr Expr Expr
  | BinOp BinOp Expr Expr
  | UnOp  UnOp  Expr
  | Var Char
    deriving (Show, Eq)

pre  op     = \[] -> Pre (UnOp op)
post op     = \[] -> Post (UnOp op)
bin  op ass = \[] -> Bin (BinOp op) ass
op' table rest = op table rest expr

expr :: ReadP Char Expr
expr = nt

nt = op' [(['¬'], pre Not)] eq

eq = op' [(['≡'], bin Eq Non)] (quest +++ disj +++ impls +++ plus)

quest = op' [(['?'], post Quest)] base

impls =
  op' [ (['⇒'], bin Impl Rght)
      , (['⇐'], bin RevImpl Lft)
      , (['I','T','E'], \[i, t] -> Pre (\e -> IfThenElse i t e))
      ]
      conj

disj =
  op' [ (['⊕'], bin Xor Rght)
      , (['∨'], bin Or  Rght)
      ]
      conj

conj = op' [(['∧'], bin And Rght)] boolNot

boolNot = op' [(['!'], pre BoolNot)] pair

plus =
  op' [ (['+'], bin Plus  Lft)
      , (['-'], bin Minus Lft)
      ]
      mul

mul =
  op' [ (['*'], bin Mul Lft)
      , (['/'], bin Div Lft)
      ]
      minus

minus = op' [(['-'], pre Neg)] pair

pair = op' [([','], bin Pair Rght)] base

base = var
       +++
       between (char '(') (char ')') expr
       +++
       liftM (\[x, y] -> BinOp Sem x y)
             (intersperseP expr ['⟦', ',', '⟧'])

var = liftM Var $ satisfy (\c -> isAscii c && isLower c)

------------------------------------------------------------------------
-- Example of a very slow parser

-- testSlow (n + 1) takes about twice as long as testSlow n (for n
-- large enough).

slow n
  | n <= 0    = char "0" >> return 0
  | otherwise = op' "+" +++ op' "-"
                --      ^^^ This choice causes the inefficiency.
                -- Note that slow (n - 1) is used in both branches.
  where op' c = op [([c ++ show n], \[] -> Pre succ)]
                   (slow (n - 1))
                   mzero

testSlow   n = parse (slow n) (map show [- n .. 0]) == [n]
testSlower n = parse (slow n) ["0"] == replicate (2 ^ n) 0

------------------------------------------------------------------------
-- Tests

test s e = do
  putStrLn $ pad 20 s ++ pad 10 (isOK ++ ":") ++ show e'
  where
  pad n s = s ++ replicate (n - length s) ' '
  e' = nub $ parse expr s
  isOK | e' == e   = "OK"
       | otherwise = "Not OK"

main = do
  test "a"       [Var 'a']
  test "¬¬(¬a)"  [UnOp Not (UnOp Not (UnOp Not (Var 'a')))]
  test "¬x≡y"    [UnOp Not (BinOp Eq (Var 'x') (Var 'y'))]
  test "x≡y≡z"   []
  test "x≡y"     [BinOp Eq (Var 'x') (Var 'y')]
  test "x≡(y≡z)" [BinOp Eq (Var 'x') (BinOp Eq (Var 'y') (Var 'z'))]
  test "x⊕y∨z"   [BinOp Xor (Var 'x') (BinOp Or (Var 'y') (Var 'z'))]
  test "x∨y?"    []
  test "y?"      [UnOp Quest (Var 'y')]
  test "x⇒y⇐z"   []
  test "IxTyEx⇒y" []
  test "x⇒y⇒z"   [BinOp Impl (Var 'x') (BinOp Impl (Var 'y') (Var 'z'))]
  test "x⇐y⇐z"   [BinOp RevImpl (BinOp RevImpl (Var 'x') (Var 'y'))
                              (Var 'z')]
  test "-a+b*c≡d⊕!(c∧d)"
       [BinOp Eq (BinOp Plus (UnOp Neg (Var 'a'))
                             (BinOp Mul (Var 'b') (Var 'c')))
                 (BinOp Xor (Var 'd')
                            (UnOp BoolNot (BinOp And (Var 'c')
                                                     (Var 'd'))))
       ]
  test "⟦x+y,z⟧*b"
       [BinOp Mul (BinOp Sem (BinOp Plus (Var 'x') (Var 'y'))
                             (Var 'z'))
                  (Var 'b')]
  test "⟦x+y,z⟧(a*b)" []
  test "⟦x+y,z⟧⟦x+y,z⟧" []
  test "⟦⟦x,y⟧,z⟧" [BinOp Sem (BinOp Sem (Var 'x') (Var 'y')) (Var 'z')]
  test "IxTyE⟦x⇒y,z⟧"
       [IfThenElse (Var 'x') (Var 'y')
                   (BinOp Sem (BinOp Impl (Var 'x') (Var 'y'))
                              (Var 'z'))]

slowMain = do
  [n] <- getArgs
  print $ testSlow $ read n
