
module Agda.Compiler.Treeless.Unused
  ( usedArguments
  , stripUnusedArguments
  ) where

import Data.Maybe

import qualified Data.Set as Set
  -- Andreas, 2021-02-10
  -- TODO: Replace Set by IntSet.
  -- However, this has to wait until we can comfortably bump to
  -- containers-0.6.3.1, which is the first to contain IntSet.mapMonotonic.
  -- Currently, such a constraints gets us into cabal hell.
  -- GHC 8.10 is still shipped with 0.6.2.1, so we either have to wait
  -- until we drop GHC 8 or until we adopt v2-cabal.

import Agda.Syntax.Treeless
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute

import Agda.Compiler.Treeless.Pretty () -- instance only

import Agda.Utils.Function ( iterateUntilM )
import Agda.Utils.List     ( downFrom )
import Agda.Utils.Pretty   ( prettyShow )

usedArguments :: QName -> TTerm -> TCM [ArgUsage]
usedArguments q t = computeUnused q b (replicate n ArgUnused)
  where (n, b) = tLamView t

-- | Saturation algorithm, starting with all unused arguments
--   and adding usages until fixed-point has been reached.

computeUnused :: QName -> TTerm -> [ArgUsage] -> TCM [ArgUsage]
computeUnused q t = iterateUntilM (==) $ \ used -> do

  reportSLn "treeless.opt.unused" 50 $ concat
    [ "Unused approximation for ", prettyShow q, ": "
    , unwords [ if u == ArgUsed then [x] else "_" | (x, u) <- zip ['a'..] used ]
    ]
  -- Update usage information q to so far "best" value.
  setCompiledArgUse q used

  -- The new usage information is the free variables of @t@,
  -- computed under the current usage assumptions of the functions it calls.
  fv <- go t
  return $ [ if Set.member i fv then ArgUsed else ArgUnused
           | i <- downFrom (length used)
           ]
  where
    go = \case
      TVar x    -> pure $ Set.singleton x
      TPrim{}   -> pure Set.empty
      TDef{}    -> pure Set.empty
      TLit{}    -> pure Set.empty
      TCon{}    -> pure Set.empty

      TApp (TDef f) ts -> do
        used <- fromMaybe [] <$> getCompiledArgUse f
        Set.unions <$> sequence [ go t | (t, ArgUsed) <- zip ts $ used ++ repeat ArgUsed ]

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

stripUnusedArguments :: [ArgUsage] -> TTerm -> TTerm
stripUnusedArguments used t = mkTLam m $ applySubst rho b
  where
    (n, b) = tLamView t
    m      = length $ filter (== ArgUsed) used'
    used'  = reverse $ take n $ used ++ repeat ArgUsed
    rho = computeSubst used'
    computeSubst (ArgUnused : bs) = TErased :# computeSubst bs
    computeSubst (ArgUsed   : bs) = liftS 1 $ computeSubst bs
    computeSubst []               = idS
