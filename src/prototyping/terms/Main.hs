
import System.Environment
import Text.PrettyPrint

import qualified Syntax.Abs as A
import Syntax.Lex
import Syntax.Par
import Syntax.ErrM

import Monad
import Check
import Term
import Eval
import Pretty

showDef (Decl x)  = return [show x]
showDef (Def x v) = do
  v1 <- reduce v
  -- v2 <- normalize v
  return [ show $ pretty x <+> text "=" <+> pretty v
         , show $ nest 2 $ text "-->" <+> pretty v1
--          , "  ==> " ++ show v2
         ]

main = do
  [file] <- getArgs
  s <- readFile file
  case pProgram (myLexer s) of
    Bad err -> putStrLn $ "Parse error: " ++ err
    Ok p    -> case runTC (checkProg p >>= mapM showDef) of
      Left err -> putStrLn $ "Scope error: " ++ err
      Right ss -> putStr $ unlines (concat ss)
