module Monad where

import           Syntax.Abstract                  (Name)
import           Definition
import qualified Impl                             as I

addConstant :: Name -> I.ConstantKind -> I.ClosedType -> I.TC v ()
addConstant x k a = I.addDefinition x (Constant x k a)

addConstructor :: Name -> Name -> I.ClosedTelescope I.Type -> I.TC v ()
addConstructor c d tel = I.addDefinition c (Constructor c d tel)

addProjection :: Name -> I.Field -> Name -> I.ClosedTelescope I.Type -> I.TC v ()
addProjection f n r tel = I.addDefinition f (Projection f n r tel)

addClause :: Name -> [Pattern] -> I.ClauseBody -> I.TC v ()
addClause f ps v = do
  def <- I.getDefinition f
  let ext (Constant x Postulate a) = Function x a [c]
      ext (Function x a cs)        = Function x a (cs ++ [c])
      ext (Constant _ k _)         = error $ "Monad.addClause " ++ show k
      ext Constructor{}            = error $ "Monad.addClause constructor"
      ext Projection{}             = error $ "Monad.addClause projection"
  I.addDefinition f (ext def)
  where
    c = Clause ps v
