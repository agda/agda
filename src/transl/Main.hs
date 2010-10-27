
{- Translator from Agda to Agda 2 -}

module Main where

import Id

import Data.Generics
import Control.Monad.State
import System.IO
import System.Environment
import Translator
import System.Console.GetOpt

data Flag = Help | Debug | OldSyntax
          deriving (Eq, Show)

options :: [OptDescr Flag]
options = [ Option ['?'] ["help"]   (NoArg Help)         "show this help"
          , Option ['D'] ["debug"]  (NoArg Debug)        "print debug messages to stderr"
	  , Option [] ["old"] (NoArg OldSyntax)		 "use old syntax"
          ]

compilerOpts :: [String] -> IO ([Flag], [String])
compilerOpts argv =
    case getOpt Permute options argv of
      (o,n,[]  ) -> return (o,n)
      (_,_,errs) -> ioError (userError (concat errs ++ usageInfo usage options))

usage :: String
usage = "usage : agda1to2 <agda1 file>"

main :: IO ()
main = do { argv <- getArgs
          ; (fs, args) <- compilerOpts argv
          ; case args of
              [file]
                -> do { cs     <- readFile file
                      ; toks   <- return $ agda1Lexer True file cs
                      ; ctree  <- return $ agda1Parser (newSyntax fs) toks
                      ; agda1to2 (trans fs) ctree
                      }
              _ -> hPutStrLn stderr usage
	  }
  where
    newSyntax fs = OldSyntax `notElem` fs
    trans fs cldfs tab = do { return ()                       -- dummy
                         ; let whenDebug = when (Debug `elem` fs) . hPutStrLn stderr
                         ; whenDebug $ show
			 $ let { (t,i)   = freshId' tab [] "add"
			       ; (t',i') = freshId' t [i] "add" }
			   in freshId' t' [i,i'] "add"
                         ; whenDebug $ show $ cldfs
                         ; ctnorm <- return $ flip evalState tab
                                            $ normalise cldfs
                         ; whenDebug $ show ctnorm
		         ; a2tree <- return $ translate ctnorm
                         ; whenDebug $ unlines $ map gshow $ a2tree
		         ; hPutStrLn stdout $ unlines $ map show $ a2tree
			 }
    normalise defs0 = do { return ()                       -- dummy
                         ; defs00 <- return $ map valueT2valueS defs0
			 ; defs10 <- return $ map elimTopLam defs00
			 ; defs20 <- return $ concatMap elimTopCase defs10
			 ; defs30 <- mapM convCase defs20
			 ; return $ concat defs30
			 }
--
-- N.B. (2006-05-29): elimTopCase and convCase do nothing.
--                    only top-level case-expression in Agda1 will be
--                    translated into Agda2 with the 'translate' function.
