{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Conversion where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

compareTerm  :: Comparison -> Type -> Term -> Term -> TCM ()
compareAs    :: Comparison -> CompareAs -> Term -> Term -> TCM ()
compareTermOnFace :: Comparison -> Term -> Type -> Term -> Term -> TCM ()
compareAtom  :: Comparison -> CompareAs -> Term -> Term -> TCM ()
compareArgs  :: [Polarity] -> [IsForced] -> Type -> Term -> Args -> Args -> TCM ()
compareElims :: [Polarity] -> [IsForced] -> Type -> Term -> [Elim] -> [Elim] -> TCM ()
compareType  :: Comparison -> Type -> Type -> TCM ()
compareSort  :: Comparison -> Sort -> Sort -> TCM ()
compareLevel :: Comparison -> Level -> Level -> TCM ()
equalTerm    :: Type -> Term -> Term -> TCM ()
equalTermOnFace :: Term -> Type -> Term -> Term -> TCM ()
equalType    :: Type -> Type -> TCM ()
equalSort    :: Sort -> Sort -> TCM ()
equalLevel   :: Level -> Level -> TCM ()
leqType      :: Type -> Type -> TCM ()
leqLevel     :: Level -> Level -> TCM ()
leqSort      :: Sort -> Sort -> TCM ()
