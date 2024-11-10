{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Compiler.Treeless.Unused
  ( usedArguments
  , stripUnusedArguments
  ) where

import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty   ( prettyShow )
import Agda.Syntax.Treeless
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute

import Agda.Compiler.Treeless.Pretty () -- instance only

import Agda.Utils.Function ( iterateUntilM )
import Agda.Utils.List     ( downFrom )
import qualified Agda.Utils.VarSet as VarSet

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
  return $ [ if VarSet.member i fv then ArgUsed else ArgUnused
           | i <- downFrom (length used)
           ]
  where
    go = \case
      TVar x    -> pure $ VarSet.singleton x
      TPrim{}   -> pure VarSet.empty
      TDef{}    -> pure VarSet.empty
      TLit{}    -> pure VarSet.empty
      TCon{}    -> pure VarSet.empty

      TApp (TDef f) ts -> do
        used <- fromMaybe [] <$> getCompiledArgUse f
        VarSet.unions <$> sequence [ go t | (t, ArgUsed) <- zip ts $ used ++ repeat ArgUsed ]

      TApp f ts -> VarSet.unions <$> mapM go (f : ts)
      TLam b    -> underBinder <$> go b
      TLet e b  -> do
        uses <- go b
        if | VarSet.member 0 uses -> VarSet.union (underBinder uses) <$> go e
           | otherwise            -> pure (underBinder uses)
      TCase x i d bs ->
        let e    = caseErased i
            cont = VarSet.unions <$> ((:) <$> go d <*> mapM (goAlt e) bs) in
        case e of
          Erased{}    -> cont
          NotErased{} -> VarSet.insert x <$> cont
      TUnit{}   -> pure VarSet.empty
      TSort{}   -> pure VarSet.empty
      TErased{} -> pure VarSet.empty
      TError{}  -> pure VarSet.empty
      TCoerce t -> go t

    goAlt _ (TALit _   b) = go b
    goAlt e (TAGuard g b) = case e of
      NotErased{} -> VarSet.union <$> go g <*> go b
      Erased{}    -> -- The guard will not be executed if the match
                     -- is on an erased argument.
                     go b
    goAlt _ (TACon _ a b) = underBinders a <$> go b

    underBinder = underBinders 1
    underBinders 0 = id
    underBinders n = VarSet.filterGE 0 . VarSet.subtract n

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
