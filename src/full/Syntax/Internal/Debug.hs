{-# OPTIONS -fglasgow-exts #-}
-- | Printing internal syntax without going through concrete syntax. Used for debugging.
module Syntax.Internal.Debug where

import Control.Monad.Reader

import Data.Char

import Syntax.Common
import Syntax.Internal

---------------------------------------------------------------------------
-- * Debugging
---------------------------------------------------------------------------

bracket :: Hiding -> String -> String
bracket Hidden	  s = "{" ++ s ++ "}"
bracket NotHidden s = "(" ++ s ++ ")"

isOp (c:_) = not $ isAlpha c
isOp [] = False

val2str :: (MonadReader Int m) => Term -> m String
val2str (Var i args) = do
    n <- ask
    args2str (if n > i then "x"++(show $ n - i) else "p"++(show $ i - n)) args
val2str (Lam (Abs _ v) args) = do
    hd <- local (+ 1) $ val2str v
    n <- ask
    args2str ("(\\x"++(show $ n + 1)++" -> "++hd++")") args
val2str (Lit l) = return $ show l
val2str (Con c [Arg NotHidden v1,Arg NotHidden v2])
    | isOp (show c) =
	do  s1 <- val2str v1
	    s2 <- val2str v2
	    return $ "(" ++ s1 ++ " " ++ show c ++ " " ++ s2 ++ ")"
val2str (Def c [Arg NotHidden v1,Arg NotHidden v2])
    | isOp (show c) =
	do  s1 <- val2str v1
	    s2 <- val2str v2
	    return $ "(" ++ s1 ++ " " ++ show c ++ " " ++ s2 ++ ")"
val2str (Def c args) = args2str (show c) args
val2str (Con c args) = args2str (show c) args
val2str (MetaV x args) = args2str ("?"++(show x)) args

typ2str :: (MonadReader Int m) => Type -> m String
typ2str (El v _) =
    do	s <- val2str v
	return $ "(El " ++ s ++ ")"
typ2str (Pi h a (Abs _ b)) = do
    aStr <- typ2str a
    bStr <- local (+ 1) $ typ2str b
    n <- ask
    return $ bracket h ("x"++(show $ n + 1)++" : "++aStr) ++ " -> "++bStr
typ2str (Sort s) = return $ srt2str s
typ2str (MetaT x args) = args2str ("?"++(show x)) args
typ2str (LamT (Abs _ a)) = do
    aStr <- local (+ 1) $ typ2str a
    n <- ask
    return $ "[x"++(show $ n + 1)++"] "++aStr

args2str :: (MonadReader Int m) => String -> Args -> m String
args2str hd [] = return hd
args2str hd (Arg h arg:args) = do
    a <- val2str arg
    args2str (hd++(if a == "" then "" else " "++bracket h a)) args

srt2str :: Sort -> String
srt2str (Type n)    = "set"++(show n)
srt2str Prop	    = "prop"
srt2str (MetaS x)   = "?"++(show x)
srt2str (Lub s1 s2) = (srt2str s1)++" \\/ "++(srt2str s2)
srt2str (Suc s)	    = show s ++ "+1"

instance Show Term where show v = runReader (val2str v) 0
instance Show Type where show a = runReader (typ2str a) 0
instance Show Sort where show   = srt2str

instance Show Clause where
    show (Clause ps b) = show ps ++ " = " ++ show b

instance Show Pattern where
    show (VarP x)    = show x
    show (ConP c ps) = "(" ++ unwords (show c : map show ps) ++ ")"

instance Show ClauseBody where
    show (Body v) = show v
    show (Bind (Abs x b)) = "\\" ++ x ++ " -> " ++ show b

