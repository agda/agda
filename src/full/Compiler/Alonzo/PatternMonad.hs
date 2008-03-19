module Compiler.Alonzo.PatternMonad where
import Syntax.Internal
import TypeChecking.Monad.Base

import Control.Monad.State
import Control.Monad.Error

import Data.Map 

import Language.Haskell.Syntax
import TypeChecking.Monad

type Defs =  Map QName Definition
data PState = PSt 
  { cnt :: Int 
  , lst :: [HsPat]
  , clause :: Clause
  , defs :: Defs
  }

initPState :: Clause -> Defs -> PState
initPState c d = PSt 
  { cnt = 0
  , lst = []
  , clause = c 
  , defs = d
  }

type PM a = StateT PState TCM a

getPDefs :: PM Defs
getPDefs = get >>= (return . defs)

getPcnt :: PM Int
getPcnt = get >>= (return . cnt)

getPlst :: PM [HsPat]
getPlst = get >>= (return . lst)

getPclause :: PM Clause
getPclause = get >>= (return . clause)

putPlst :: [HsPat] -> PM()
putPlst newlst = modify $ \s -> s { lst = newlst }

putPcnt :: Int -> PM()
putPcnt newcnt = modify $ \s -> s { cnt = newcnt }


incPcnt :: PM()
incPcnt = do
        n <- getPcnt
        putPcnt (n+1)


addWildcard :: PM()
addWildcard = do 
        lst <- getPlst
        putPlst $ lst++[HsPWildCard]

addVar :: Int -> PM()
addVar n = do
        lst <- getPlst
        putPlst $ lst++[HsPVar(HsIdent ("v" ++ (show n)))]
