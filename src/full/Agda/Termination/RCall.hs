module Agda.Termination.RCall where

import Agda.Syntax.Internal as I
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Abstract.Pretty
import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Position(noRange)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Errors

import Agda.Termination.Utils

import Agda.Utils.Pretty
import Agda.Utils.Monad

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans
import qualified Data.Map as Map
import Data.List as List
import Text.PrettyPrint

data  RCall = RCall {
   callFun :: QName,
   callClause :: Int,
   callNumber :: Int,
   callArgs :: Args
} 


instance PrettyTCM RCall where
  prettyTCM r = do
		  dr <- prettyTCM $ callFun r
		  dargs <- prettyTCM  (callArgs r)
		  return $ dr

instance PrettyTCM  a => PrettyTCM [a] where
  prettyTCM [] = return $ text ""
  prettyTCM (r:rs) = do 
			dr <- prettyTCM r 
			ds <- prettyTCM rs
                        return $ dr <> comma <> ds

