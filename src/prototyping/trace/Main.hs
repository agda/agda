
module Main where

import Lambda.Par
import Lambda.Print
import Lambda.ErrM

import TypeChecker

main = do
    s <- getContents
    mapM_ action $ lines s

action s =
    case pExp $ myLexer s of
	Ok e	-> do
	    putStrLn ""
	    putStrLn $ printTree e
	    case runTC $ infer e of
		Left (tr,s)	-> do
		    putStrLn $ "ERROR " ++ s
		    putStr $ indent 2 $ show tr
		Right t ->
		    putStrLn $ "OK " ++ printTree t
	Bad err -> putStrLn err

