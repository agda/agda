
module Agda.TypeChecking.Polarity where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Error
import Data.List

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Positivity

getArity :: QName -> TCM Arity
getArity x = do
  def <- theDef <$> getConstInfo x
  case def of
    Axiom{}                                      -> return 0
    Function{ funClauses = Clause _ _ ps _ : _ } -> return $ genericLength ps
    Function{ funClauses = [] }                  -> return 0
    Datatype{ dataPars = np, dataIxs = ni }      -> return np --- TODO: what about indices?
    Record{ recPars = n }                        -> return n
    Constructor{}                                -> return 0
    Primitive{}                                  -> return 0

computePolarity :: QName -> TCM ()
computePolarity x = do
  reportSLn "tc.polarity.set" 15 $ "Computing polarity of " ++ show x
  n <- getArity x
  reportSLn "tc.polarity.set" 20 $ "  arity = " ++ show n
  pol <- mapM getPol [0..n - 1]
  reportSLn "tc.polarity.set" 10 $ "Polarity of " ++ show x ++ ": " ++ show pol
  setPolarity x pol
  where
    getPol :: Nat -> TCM Polarity
    getPol i = do
        evalStateT (checkPosArg x i) initPosState
        return Covariant
      `catchError` \_ -> return Invariant

