module Agda.Interaction.SearchAbout (findMentions) where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import qualified Data.Map as Map
import Data.List (isInfixOf)
import Data.Either (partitionEithers)

import Agda.Syntax.Position (Range)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.TypeChecking.Monad
import qualified Agda.Syntax.Common as Com
import Agda.Syntax.Internal
import Agda.Interaction.BasicOps (normalForm)
import qualified Agda.Syntax.Translation.ConcreteToAbstract as TCA
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C

import Agda.Interaction.BasicOps
import Debug.Trace

collectNamesInType :: Type -> [A.QName]
collectNamesInType = collectNamesInTerm . unEl

collectNamesInTerm :: Term -> [A.QName]
collectNamesInTerm (Var _ els)  = collectNamesInElims els
collectNamesInTerm (Lam ty t)   = collectNamesInTerm $ unAbs t
collectNamesInTerm (Def n els)  = n : collectNamesInElims els
collectNamesInTerm (Con n _ args) = conName n : collectNamesInArgs args
collectNamesInTerm (Pi dom cod) = collectNamesInType (Com.unDom dom) ++ collectNamesInType (unAbs cod)
collectNamesInTerm (Shared t)   = collectNamesInTerm $ ignoreSharing $ derefPtr t
collectNamesInTerm _            = []

collectNamesInElims :: Elims -> [A.QName]
collectNamesInElims = concatMap collectNamesInElim

collectNamesInElim :: Elim -> [A.QName]
collectNamesInElim (Apply a) = collectNamesInTerm $ Com.unArg a
collectNamesInElim (Proj _ n)= [n]
collectNamesInElim (IApply x y a) = concatMap collectNamesInTerm [x,y,a]

collectNamesInArgs :: Args -> [A.QName]
collectNamesInArgs = concatMap (collectNamesInTerm . Com.unArg)

findMentions :: Rewrite -> Range -> String -> TCM [(C.Name, Type)]
findMentions norm rg nm = do
  let (strs, nms) = partitionEithers $ fmap isString $ words nm
  cnms <- mapM (parseName rg) nms
  rnms <- mapM resolveName cnms
  let defs = fmap (fmap anameName . anames) rnms
  scp  <- getNamedScope =<< currentModule
  let names = nsNames $ allThingsInScope scp
  concat <$> mapM (\ (x, n) -> do
              t <- normalForm norm =<< typeOfConst (anameName n)
              let defName  = show x
              let namesInT = collectNamesInType t
              return $ do
                guard (all (`isInfixOf` defName) strs)
                guard (all (any (`elem` namesInT)) defs)
                return (x, t)
           ) (concatMap (\ (x, ns) -> map ((,) x) ns) $ Map.toList names)
  where
    isString str
      |  not (null str)
      && head str == '"'
      && last str == '"' = Left $ filter (/= '"') str
      | otherwise        = Right str

    anames (DefinedName _ an)     = [an]
    anames (FieldName     ans)    = ans
    anames (ConstructorName ans)  = ans
    anames (PatternSynResName an) = [an]
    anames _                      = []
