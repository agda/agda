
module Agda.TypeChecking.Telescope.Path where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Control.Monad (unless, guard)

import Data.Foldable (forM_, find)
import qualified Data.List as List
import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Position

import Agda.TypeChecking.Free
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Size

import Agda.Utils.Impossible


-- | In an ambient context Γ, @telePiPath f Δ t bs@ builds a type that
-- can be @telViewPathBoundaryP'ed@ into (TelV Δ t, bs').
--   Γ.Δ ⊢ t
--   bs = [(i,u_i)]
--   Δ = Δ0,(i : I),Δ1
--   ∀ b ∈ {0,1}.  Γ.Δ0 | u_i .b : (telePiPath f Δ1 t bs)(i = b)
--   Γ ⊢ telePiPath f Δ t bs
telePiPath :: (Abs Type -> Abs Type) -> Telescope -> Type -> Boundary -> TCM Type
telePiPath reAbs tel t bs = do
  pp <- primPathP
  io <- primIOne
  let
    argN = Arg defaultArgInfo
    argH = Arg $ setHiding Hidden defaultArgInfo
    getLevel :: Abs Type -> TCM Level
    getLevel b = do
      s <- reduce $ getSort <$> b
      case s of
        NoAbs _ (Type l) -> return l
        Abs n (Type l) | NoOccurrence <- occurrence 0 s -> return $ noabsApp __IMPOSSIBLE__ (Abs n l)
        _ -> typeError . GenericError . show =<<
             (text "The type is non-fibrant or its sort depends on an interval variable" <+> prettyTCM (unAbs b))
             -- TODO better Type Error
    telePiPath :: [Int] -> Telescope -> TCM Type
    telePiPath []     EmptyTel          = pure $ t
    telePiPath (x:xs) (ExtendTel a tel)
      = case List.find (\ (t,_) -> t == var x) bs of
          Just (_,u) -> do
            -- assume a = 𝕀
            b <- b
            l <- getLevel b
            return $ El (Type l) $
              pp `apply` [ argH (Level l)
                         , argN (Lam defaultArgInfo (unEl <$> b))
                         , argN $ fst u
                         , argN $ snd u
                         ]
          Nothing    -> do
            b <- b
            return $ El (piSort (getSort a) (getSort <$> b)) (Pi a (reAbs b))
      where
        b  = traverse (telePiPath xs) tel
    telePiPath _     EmptyTel = __IMPOSSIBLE__
    telePiPath []    _        = __IMPOSSIBLE__
  telePiPath (downFrom (size tel)) tel


iApplyVars :: DeBruijn a => [NamedArg (Pattern' a)] -> [Int]
iApplyVars ps = flip concatMap (map namedArg ps) $ \case
                             IApplyP _ t u x ->
                               [fromMaybe __IMPOSSIBLE__ (deBruijnView x)]
                             VarP{} -> []
                             ProjP{}-> []
                             LitP{} -> []
                             DotP{} -> []
                             DefP _ _ ps -> iApplyVars ps
                             ConP _ _ ps -> iApplyVars ps
