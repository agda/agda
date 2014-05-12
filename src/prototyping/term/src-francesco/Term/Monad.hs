{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
module Term.Monad where

import Prelude hiding (pi)

import           Syntax.Abstract                  (Name)
import           Term.Types
import           Term.Monad.Base

addConstant :: Name -> ConstantKind -> ClosedType -> TC v ()
addConstant x k a = addDefinition x (Constant x k a)

addConstructor :: Name -> Name -> ClosedTelescope Type -> TC v ()
addConstructor c d tel = addDefinition c (Constructor c d tel)

addProjection :: Name -> Field -> Name -> ClosedTelescope Type -> TC v ()
addProjection f n r tel = addDefinition f (Projection f n r tel)

addClause :: Name -> [Pattern] -> ClauseBody -> TC v ()
addClause f ps v = do
  def <- getDefinition f
  let ext (Constant x Postulate a) = Function x a [c]
      ext (Function x a cs)        = Function x a (cs ++ [c])
      ext (Constant _ k _)         = error $ "Monad.addClause " ++ show k
      ext Constructor{}            = error $ "Monad.addClause constructor"
      ext Projection{}             = error $ "Monad.addClause projection"
  addDefinition f (ext def)
  where
    c = Clause ps v
