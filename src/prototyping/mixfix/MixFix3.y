{
module MixFix3 where

import Data.Maybe
import Data.Char
import Utils.IO
import Prelude hiding (putStrLn, print)
}

%name expr E0
%tokentype { Token }
%error { parseError }
%monad { Maybe } { (>>=) } { return }

%token
  var { TVar $$ }
  '+' { TPlus }
  '-' { TMinus }
  '*' { TMul }
  '/' { TDiv }
  '∧' { TAnd }
  '∨' { TOr }
  '⊕' { TXor }
  '≡' { TEq }
  '⇒' { TImpl }
  '⇐' { TRevImpl }
  ',' { TPair }
  '⟦' { TSemL }
  '⟧' { TSemR }
  '!' { TBoolNot }
  '¬' { TNot }
  '?' { TQuest }
  '(' { TLPar }
  ')' { TRPar }
  'I' { TIf }
  'T' { TThen }
  'E' { TElse }

%%

E0 :: { Expr }
   : '¬' E0 { UnOp Not $2 }
   | E1     { $1 }

E1 : E2 '≡' E2 { BinOp Eq $1 $3 }
   | E2        { $1 }

E2 : E3 { $1 }
   | E4 { $1 }
   | E5 { $1 }
   | E6 { $1 }

E3 : E3 '?' { UnOp Quest $1 }
   | Base   { $1 }

E4 : E7 '⊕' E4 { BinOp Xor $1 $3 }
   | E7 '∨' E4 { BinOp Or  $1 $3 }
   | E7        { $1 }

E5 : E7 '⇒' E5            { BinOp Impl    $1 $3 }
   | E5 '⇐' E7            { BinOp RevImpl $1 $3 }
   | 'I' E0 'T' E0 'E' E5 { IfThenElse $2 $4 $6 }
   | E7                   { $1 }

E6 : E6 '+' E8 { BinOp Plus  $1 $3 }
   | E6 '-' E8 { BinOp Minus $1 $3 }
   | E8        { $1 }

E7 : E9 '∧' E7 { BinOp And $1 $3 }
   | E9        { $1 }

E8 : E8 '*' E10 { BinOp Mul $1 $3 }
   | E8 '/' E10 { BinOp Div $1 $3 }
   | E10        { $1 }

E9 : '!' E9 { UnOp BoolNot $2 }
   | E11    { $1 }

E10 : '-' E10 { UnOp Neg $2 }
    | E11     { $1 }

E11 : Base ',' E11 { BinOp Pair $1 $3 }
    | Base         { $1 }

Base : var               { Var $1 }
     | '(' E0 ')'        { $2 }
     | '⟦' E0 ',' E0 '⟧' { BinOp Sem $2 $4 }

{
data Token =
    TVar Char
  | TLPar | TRPar
  | TPlus | TMinus | TMul | TDiv | TAnd | TOr | TXor | TEq
  | TImpl | TRevImpl | TPair | TSemL | TSemR
  | TBoolNot | TNot | TQuest
  | TIf | TThen | TElse
    deriving (Show)

lexer :: String -> Maybe [Token]
lexer = mapM lexChar
  where
  lexChar c | isAscii c && isLower c = Just $ TVar c
  lexChar '+' = Just TPlus
  lexChar '-' = Just TMinus
  lexChar '*' = Just TMul
  lexChar '/' = Just TDiv
  lexChar '∧' = Just TAnd
  lexChar '∨' = Just TOr
  lexChar '⊕' = Just TXor
  lexChar '≡' = Just TEq
  lexChar '⇒' = Just TImpl
  lexChar '⇐' = Just TRevImpl
  lexChar ',' = Just TPair
  lexChar '⟦' = Just TSemL
  lexChar '⟧' = Just TSemR
  lexChar '!' = Just TBoolNot
  lexChar '¬' = Just TNot
  lexChar '?' = Just TQuest
  lexChar '(' = Just TLPar
  lexChar ')' = Just TRPar
  lexChar 'I' = Just TIf
  lexChar 'T' = Just TThen
  lexChar 'R' = Just TElse
  lexChar _   = Nothing

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

parseError = const Nothing

parse :: String -> Maybe Expr
parse s = expr =<< lexer s

test s e = do
  putStrLn $ pad 20 s ++ pad 10 (isOK ++ ":") ++ show e'
  where
  pad n s = s ++ replicate (n - length s) ' '
  e' = parse s
  isOK | e' == listToMaybe e = "OK"
       | otherwise           = "Not OK"

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

}
