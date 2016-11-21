-- -- RETIRED
-- -- Andreas, 2013-10-18

-- {-# LANGUAGE CPP #-}

-- module Agda.TypeChecking.Eliminators where

-- import Data.Maybe (isJust, isNothing)

-- import Agda.Syntax.Common hiding (Arg)
-- import Agda.Syntax.Internal

-- import Agda.TypeChecking.Monad
-- import Agda.TypeChecking.Substitute
-- import Agda.TypeChecking.Reduce
-- import Agda.TypeChecking.Level
-- import {-# SOURCE #-} Agda.TypeChecking.Pretty

-- import Agda.Utils.Tuple

-- #include "undefined.h"
-- import Agda.Utils.Impossible

-- -- | Weak head normal form in elimination presentation.
-- data ElimView
--   = VarElim  Nat    [Elim]   -- ^ Neutral term @x es@.
--   | DefElim  QName  [Elim]   -- ^ Irreducible function application @f es@.
--   | ConElim  ConHead Args    -- ^ Only 'Apply' eliminations @c vs@.
-- --  | ConElim  QName  [Elim]   -- ^ Only 'Apply' eliminations @c vs@.
--   | MetaElim MetaId [Elim]   -- ^ Stuck on meta variable @X es@.
--   | NoElim   Term
--   deriving (Show)

-- data ElimViewConf = ElimViewConf { elViewReduce :: Bool, elViewProjLike :: Bool }

-- defaultElimViewConf = ElimViewConf True True
-- terminationElimViewConf = ElimViewConf False False

-- elimView :: Term -> TCM ElimView
-- elimView = elimView' defaultElimViewConf

-- elimView' :: ElimViewConf -> Term -> TCM ElimView
-- elimView' conf v = do
--   let elimView = elimView' conf
--   -- We can't assume that v has been reduced here in recursive calls,
--   -- since reducing a stuck application doesn't necessarily reduce all
--   -- the arguments.
--   v <- if elViewReduce conf then unLevel =<< reduce v else instantiate v
--   -- domi 2012-7-24: Add unLevel to handle neutral levels. The problem is that reduce turns
--   -- suc (neutral) into Level (Max [Plus 1 (NeutralLevel neutral)]) which the below pattern
--   -- match does not handle.
--   let noElim = return $ NoElim v
--   reportSDoc "tc.conv.elim" 30 $ text "elimView of " <+> prettyTCM v
--   reportSLn "tc.conv.elim" 50 $ "v = " ++ show v
--   case ignoreSharing v of
--     Def f [] -> return $ DefElim f [] -- Andreas, 2013-03-05 it is not impossible that f is an unapplied projection
--     Def f vs@(rv : vs') -> do
--       let defElim = DefElim f `app` vs
--       proj <- isProjection f
--       case proj of
--         Just Projection{ projProper = proper, projIndex = n }
--           | n > 0 && (proper || elViewProjLike conf) -> do
--                 ev <- elimView (unArg rv)
--                 case ev of
--                  -- Andreas, 2013-10-14 Since the termination checker does not reduce,
--                  -- the following 2 cases are actually possible. (Issue 918)
--                   NoElim{}  -> defElim
--                   ConElim{} -> defElim
--                   _         -> return $ elim (Proj f : map Apply vs') ev
--         _ -> defElim
--     Var x vs   -> VarElim x `app` vs
--     Con c ci vs   -> return $ ConElim c vs
-- --    Con c ci vs   -> ConElim c `app` vs
--     MetaV m vs -> MetaElim m `app` vs
--     Lam{}      -> noElim
--     Lit{}      -> noElim
--     Level{}    -> noElim
--     Sort{}     -> noElim
--     Pi{}       -> noElim
--     DontCare{} -> noElim
--     Shared p   -> __IMPOSSIBLE__
--     where
--       app f vs = return $ f $ map Apply vs
--       elim :: [Elim] -> ElimView -> ElimView
--       elim _    NoElim{}        = __IMPOSSIBLE__
--       elim es2 (VarElim  x es1) = VarElim  x (es1 ++ es2)
--       elim es2 (DefElim  x es1) = DefElim  x (es1 ++ es2)
--       elim es2 (ConElim  x es1) = __IMPOSSIBLE__
--       -- elim es2 (ConElim  x es1) = ConElim  x (es1 ++ map argFromElim es2)
--       elim es2 (MetaElim x es1) = MetaElim x (es1 ++ es2)


-- unElimView :: ElimView -> Term
-- unElimView v = case v of
--   VarElim x es  -> unElim (Var x []) es
--   DefElim x es  -> unElim (Def x []) es
--   ConElim x vs  -> unElim (Con x ci []) $ map Apply vs
--   MetaElim x es -> unElim (MetaV x []) es
--   NoElim v      -> v

-- unElim :: Term -> Elims -> Term
-- unElim v []             = v
-- unElim v (Apply u : es) = unElim (v `apply` [u]) es
-- unElim v (Proj f : es)  = unElim (Def f [defaultArg v]) es



-- -- | Take @n@ initial arguments from elimination vector.
-- takeArgsFromElims :: (Functor f, IsProjElim (f Elim)) =>
--   Int -> [f Elim] -> ([f (Arg Term)], [f Elim])
-- takeArgsFromElims 0  es            = ([], es)
-- takeArgsFromElims n []             = __IMPOSSIBLE__
-- takeArgsFromElims n (e : es)
--   | isJust (isProjElim e) = __IMPOSSIBLE__
--   | otherwise    = mapFst (fmap argFromElim e :) $ takeArgsFromElims (n-1) es

-- {-
-- takeArgsFromElims :: Int -> [Elim] -> (Args, [Elim])
-- takeArgsFromElims 0  es            = ([], es)
-- takeArgsFromElims n (Apply u : es) = mapFst (u :) $ takeArgsFromElims (n-1) es
-- takeArgsFromElims n (Proj{}  : es) = __IMPOSSIBLE__
-- -}
