
module Names where

{-

import Data.Set

import AbsCore

freeIn :: Ident -> Term -> Bool
freeIn x t = x `member` freeVars t

getVars :: (Ident -> Set Ident -> Set Ident) -> Term -> Set Ident
getVars bind t =
    case t of
	Var x	-> singleton x
	Lam x t	-> bind x $ freeVars t
	App s t	-> freeVars s `union` freeVars t
	Set	-> empty
	El	-> empty
	Fun	-> empty

freeVars :: Term -> Set Ident
freeVars = getVars delete

allVars :: Term -> Set Ident
allVars = getVars insert

freshVar :: Ident -> Set Ident -> Ident
freshVar x taken = head [ x' | x' <- versionsOf x, not $ member x' taken ]

versionsOf :: Ident -> [Ident]
versionsOf (Ident x) = Prelude.map (Ident . (x ++) . show) [0..]

-}
