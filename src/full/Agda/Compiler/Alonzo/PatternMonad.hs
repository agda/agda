module Agda.Compiler.Alonzo.PatternMonad where
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base

import Control.Monad.State
import Control.Monad.Error

import qualified Data.Map
import Data.Map (Map)

import Language.Haskell.Syntax
import Agda.TypeChecking.Monad
import Agda.Utils.Permutation
import Agda.Utils.Size

type Defs =  Map QName Definition
data PState = PSt
  { cnt :: Int
  , vars :: [Int]
  , lst :: [HsPat]
  , clause :: Clause
  , defs :: Defs
  }

initPState :: Clause -> Defs -> PState
initPState c@(Clause{ clausePerm = perm }) d = PSt
  { cnt = 0
  , vars = permute perm [0..]
  , lst = []
  , clause = c
  , defs = d
  }

type PM a = StateT PState TCM a

getPDefs :: PM Defs
getPDefs = gets defs

getPcnt :: PM Int
getPcnt = gets cnt

getPlst :: PM [HsPat]
getPlst = gets lst

getPclause :: PM Clause
getPclause = gets clause

putPlst :: [HsPat] -> PM()
putPlst newlst = modify $ \s -> s { lst = newlst }

putPcnt :: Int -> PM()
putPcnt newcnt = modify $ \s -> s { cnt = newcnt }

incPcnt :: PM()
incPcnt = modify $ \s -> s { cnt = 1 + cnt s }

addWildcard :: PM()
addWildcard = do
        lst <- getPlst
        putPlst $ lst++[HsPWildCard]

addVar :: PM()
addVar = do
        lst <- getPlst
        s <- get
        let v : vs = vars s
        put $ s { vars = vs }
        putPlst $ lst++[HsPVar(HsIdent ("v" ++ show v))]
