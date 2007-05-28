module Compiler.Alonzo.PatternMonad where
import Syntax.Internal

import Control.Monad.State
import Control.Monad.Error

import Language.Haskell.Syntax

data PState = PSt 
  { cnt :: Int 
  , lst :: [HsPat]
  , clause :: Clause
  }

initPState :: Clause -> PState
initPState c = PSt 
  { cnt = 0
  , lst = []
  , clause = c 
  }

type PM a = State PState a

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
