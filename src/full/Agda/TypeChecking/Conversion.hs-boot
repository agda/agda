
module Agda.TypeChecking.Conversion where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

compareTerm  :: Comparison -> Type -> Term -> Term -> TCM ()
compareAtom  :: Comparison -> Type -> Term -> Term -> TCM ()
compareArgs  :: [Polarity] -> Type -> Term -> Args -> Args -> TCM ()
compareElims :: [Polarity] -> Type -> Term -> [Elim] -> [Elim] -> TCM ()
compareType  :: Comparison -> Type -> Type -> TCM ()
compareTel   :: Type -> Type -> Comparison -> Telescope -> Telescope -> TCM ()
compareSort  :: Comparison -> Sort -> Sort -> TCM ()
equalTerm    :: Type -> Term -> Term -> TCM ()
equalType    :: Type -> Type -> TCM ()
equalSort    :: Sort -> Sort -> TCM ()
leqType      :: Type -> Type -> TCM ()
