
module Agda.Compiler.Treeless.Unused
  ( usedArguments
  , stripUnusedArguments
  ) where

import qualified Data.Set as Set

import Agda.Syntax.Treeless
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute

import Agda.Compiler.Treeless.Pretty () --instance only

import Agda.Utils.Pretty (prettyShow)

usedArguments :: QName -> TTerm -> TCM [Bool]
usedArguments q t = computeUnused q b (replicate n False)
  where (n, b) = tLamView t

computeUnused :: QName -> TTerm -> [Bool] -> TCM [Bool]
computeUnused q t used = do
  reportSLn "treeless.opt.unused" 50 $ "Unused approximation for " ++ prettyShow q ++ ": " ++
                                       unwords [ if u then [x] else "_" | (x, u) <- zip ['a'..] used ]
  setCompiledArgUse q used
  fv <- go t
  let used' = [ Set.member i fv | (i, _) <- reverse $ zip [0..] used ]
  if used == used' then return used'
                   else computeUnused q t used'
  where
    go t = case t of
      TVar x    -> pure $ Set.singleton x
      TPrim{}   -> pure Set.empty
      TDef{}    -> pure Set.empty
      TLit{}    -> pure Set.empty
      TCon{}    -> pure Set.empty

      TApp (TDef f) ts -> do
        used <- getCompiledArgUse f
        Set.unions <$> sequence [ go t | (t, True) <- zip ts $ used ++ repeat True ]

      TApp f ts -> Set.unions <$> mapM go (f : ts)
      TLam b    -> underBinder <$> go b
      TLet e b  -> do
        uses <- go b
        if | Set.member 0 uses -> Set.union (underBinder uses) <$> go e
           | otherwise         -> pure (underBinder uses)
      TCase x _ d bs -> Set.insert x . Set.unions <$> ((:) <$> go d <*> mapM goAlt bs)
      TUnit{}   -> pure Set.empty
      TSort{}   -> pure Set.empty
      TErased{} -> pure Set.empty
      TError{}  -> pure Set.empty
      TCoerce t -> go t

    goAlt (TALit _   b) = go b
    goAlt (TAGuard g b) = Set.union <$> go g <*> go b
    goAlt (TACon _ a b) = underBinders a <$> go b

    underBinder = underBinders 1
    underBinders 0 = id
    underBinders n = Set.filter (>= 0) . Set.mapMonotonic (subtract n)

stripUnusedArguments :: [Bool] -> TTerm -> TTerm
stripUnusedArguments used t = mkTLam m $ applySubst rho b
  where
    (n, b) = tLamView t
    m      = length $ filter id used'
    used'  = reverse $ take n $ used ++ repeat True
    rho = computeSubst used'
    computeSubst (False : bs) = TErased :# computeSubst bs
    computeSubst (True  : bs) = liftS 1 $ computeSubst bs
    computeSubst []           = idS
