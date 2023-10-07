{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE NondecreasingIndentation #-}
module Agda.TypeChecking.Telescope.Path where

import Prelude hiding (null)

import qualified Data.List as List
import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Free
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Size

import Agda.Utils.Impossible


-- | In an ambient context Γ, @telePiPath f lams Δ t bs@ builds a type that
-- can be @telViewPathBoundaryP'ed@ into (TelV Δ t, bs').
--   Γ.Δ ⊢ t
--   bs = [(i,u_i)]
--   Δ = Δ0,(i : I),Δ1
--   ∀ b ∈ {0,1}.  Γ.Δ0 | lams Δ1 (u_i .b) : (telePiPath f Δ1 t bs)(i = b) -- kinda: see lams
--   Γ ⊢ telePiPath f Δ t bs
telePiPath :: (Abs Type -> Abs Type) -> ([Arg ArgName] -> Term -> Term) -> Telescope -> Type -> Boundary -> TCM Type
telePiPath reAbs lams tel t bs = do
  mpp <- getTerm' builtinPathP
  io <- primIOne
  let
    argN = Arg defaultArgInfo
    argH = Arg $ setHiding Hidden defaultArgInfo
    getLevel :: Abs Type -> TCM Level
    getLevel b = do
      s <- reduce $ getSort <$> b
      case s of
        NoAbs _ (Type l) -> return l
        Abs n (Type l) | not (freeIn 0 s) -> return $ noabsApp __IMPOSSIBLE__ (Abs n l)
        _ -> typeError . GenericError . show =<<
             (text "The type is non-fibrant or its sort depends on an interval variable" <+> prettyTCM (unAbs b))
             -- TODO better Type Error
    telePiPath :: [Int] -> Telescope -> TCM Type
    telePiPath []     EmptyTel          = pure $ t
    telePiPath (x:xs) (ExtendTel a tel)
      = case List.find (\ (t,_) -> t == var x) bs of
          Just (_,u) -> do
            let pp = fromMaybe __IMPOSSIBLE__ mpp
            let names = teleArgNames $ unAbs tel
            -- assume a = 𝕀
            b <- b
            l <- getLevel b
            return $ El (Type l) $
              pp `apply` [ argH (Level l)
                         , argN (Lam defaultArgInfo (unEl <$> b))
                         , argN $ lams names (fst u)
                         , argN $ lams names (snd u)
                         ]
          Nothing    -> do
            b <- b
            return $ El (mkPiSort a b) (Pi a (reAbs b))
      where
        b  = traverse (telePiPath xs) tel
    telePiPath _     EmptyTel = __IMPOSSIBLE__
    telePiPath []    _        = __IMPOSSIBLE__
  telePiPath (downFrom (size tel)) tel

-- | @telePiPath_ Δ t [(i,u)]@
--   Δ ⊢ t
--   i ∈ Δ
--   Δ ⊢ u_b : t  for  b ∈ {0,1}
telePiPath_ :: Telescope -> Type -> [(Int,(Term,Term))] -> TCM Type
telePiPath_ tel t bndry = do
  reportSDoc "tc.tel.path" 40                  $ text "tel  " <+> prettyTCM tel
  reportSDoc "tc.tel.path" 40 $ addContext tel $ text "type " <+> prettyTCM t
  reportSDoc "tc.tel.path" 40 $ addContext tel $ text "bndry" <+> pretty bndry

  telePiPath id argsLam tel t [(var i, u) | (i , u) <- bndry]
 where
   argsLam args tm = strengthenS impossible 1 `applySubst`
     foldr (\ Arg{argInfo = ai, unArg = x} -> Lam ai . Abs x) tm args

-- | arity of the type, including both Pi and Path.
--   Does not reduce the type.
arityPiPath :: Type -> TCM Int
arityPiPath t = do
  piOrPath t >>= \case
    Left (_, u) -> (+1) <$> arityPiPath (unAbs u)
    Right _     -> return 0

-- | Collect the interval copattern variables as list of de Bruijn indices.
class IApplyVars p where
  iApplyVars :: p -> [Int]

instance DeBruijn a => IApplyVars (Pattern' a) where
  iApplyVars = \case
    IApplyP _ t u x -> [ fromMaybe __IMPOSSIBLE__ $ deBruijnView x ]
    VarP{}          -> []
    ProjP{}         -> []
    LitP{}          -> []
    DotP{}          -> []
    DefP _ _ ps     -> iApplyVars ps
    ConP _ _ ps     -> iApplyVars ps

instance IApplyVars p => IApplyVars (NamedArg p) where
  iApplyVars = iApplyVars . namedArg

instance IApplyVars p => IApplyVars [p] where
  iApplyVars = concatMap iApplyVars

{-# SPECIALIZE isInterval :: Type -> TCM Bool #-}
-- | Check whether a type is the built-in interval type.
isInterval :: (MonadTCM m, MonadReduce m) => Type -> m Bool
isInterval t = liftTCM $ do
  caseMaybeM (getName' builtinInterval) (return False) $ \ i -> do
  reduce (unEl t) <&> \case
    Def q [] -> q == i
    _        -> False
