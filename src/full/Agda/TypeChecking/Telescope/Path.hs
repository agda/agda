{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE NondecreasingIndentation #-}
module Agda.TypeChecking.Telescope.Path where

import Prelude hiding (null)

import qualified Data.List as List
import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive.Base (argE)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Size

import Agda.Utils.Impossible


-- | In an ambient context Γ, @telePiPath f lams Δ t bs@ builds a type that
-- can be @'telViewPathBoundary'@ed into (TelV Δ t, bs').
--   Γ.Δ ⊢ t
--   bs = [(i,u_i)]
--   Δ = Δ0,(i : I),Δ1
--   ∀ b ∈ {0,1}.  Γ.Δ0 | lams Δ1 (u_i .b) : (telePiPath f Δ1 t bs)(i = b) -- kinda: see lams
--   Γ ⊢ telePiPath f Δ t bs
telePiPath :: (Abs Type -> Abs Type) -> ([Arg ArgName] -> Term -> Term) -> Telescope -> Type -> Boundary -> TCM Type
telePiPath = \ reAbs lams tel t (Boundary bs) -> do
  pathP <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinPathP
  let
    loop :: [Int] -> Telescope -> TCM Type
    loop []     EmptyTel          = return t
    loop (x:xs) (ExtendTel a tel) = do
        b <- traverse (loop xs) tel
        case List.find ((x ==) . fst) bs of
          -- Create a Path type.
          Just (_,(u0,u1)) -> do
            let names = teleArgNames $ unAbs tel
            -- assume a = 𝕀
            l <- getLevel b
            argL <- argE (Level l)
            return $ El (Type l) $
              pathP `apply`
                [ argL
                , argN (Lam defaultArgInfo (unEl <$> b))
                , argN $ lams names u0
                , argN $ lams names u1
                ]
          Nothing    -> do
            -- Create a Π type.
            return $ El (mkPiSort a b) (Pi a (reAbs b))
    loop (_:_) EmptyTel    = __IMPOSSIBLE__
    loop []    ExtendTel{} = __IMPOSSIBLE__
  loop (downFrom (size tel)) tel
  where
    argN = Arg defaultArgInfo
    argH = Arg $ setHiding Hidden defaultArgInfo
    getLevel :: Abs Type -> TCM Level
    getLevel b = do
      s <- reduce $ getSort <$> b
      -- 'reAbs' ensures that 'Abs' correctly indicates an occurrence of the bound variable.
      case reAbs s of
        NoAbs _ (Type l) -> return l
        _ -> typeError $ PathAbstractionFailed b
          -- Andreas, 2025-04-17, not impossible after all, see issue #7803.
          --
          -- Previously: 2024-10-07, issue #7413
          -- Andrea writes in https://github.com/agda/agda/issues/7413#issuecomment-2396146135
          --
          -- I believe this is actually impossible at the moment
          -- unless generalized Path types were implemented while I wasn't looking:
          --
          -- telePathPi only does this check if there's a boundary,
          -- which should only be introduced by a PathP copattern,
          -- which then should ensure the result type is in Type lvl
          -- for some lvl that does not depend on on the interval
          -- variable of the path.

-- | @telePiPath_ Δ t [(i,u)]@
--   Δ ⊢ t
--   i ∈ Δ
--   Δ ⊢ u_b : t  for  b ∈ {0,1}
telePiPath_ :: Telescope -> Type -> Boundary -> TCM Type
telePiPath_ tel t bndry = do
  reportSDoc "tc.tel.path" 40                  $ text "tel  " <+> prettyTCM tel
  reportSDoc "tc.tel.path" 40 $ addContext tel $ text "type " <+> prettyTCM t
  reportSDoc "tc.tel.path" 40 $ addContext tel $ text "bndry" <+> pretty bndry

  telePiPath id argsLam tel t bndry
 where
   argsLam args tm = strengthenS impossible 1 `applySubst`
     foldr (\ Arg{argInfo = ai, unArg = x} -> Lam ai . Abs x) tm args

-- | arity of the type, including both Pi and Path.
--   Does not reduce the type.
arityPiPath :: Type -> TCM Int
arityPiPath t = do
  piOrPath t >>= \case
    Left (_, u) -> (+ 1) <$> arityPiPath (unAbs u)
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
isInterval :: (MonadTCM m) => Type -> m Bool
isInterval t = liftTCM $ do
  caseMaybeM (getName' builtinInterval) (return False) $ \ i -> do
  reduce (unEl t) <&> \case
    Def q [] -> q == i
    _        -> False
