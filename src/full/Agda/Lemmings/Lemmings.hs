-- | Lemmings is the backbone of a new search tool for Agda
--   and is currently under-development.
--
--  Once complete, Lemmings will allow the user to gain a list of viable
--  lemmas or proofs that could be applied in some form to the current goal
--  and/or search for proofs/functions/datatypes in a similar fashion to
--  Hoogle
module Agda.Lemmings.Lemmings where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.Except (catchError)

import Data.List as List
import qualified Data.Map as Map

import Agda.Interaction.Base (Rewrite(..))
import Agda.Interaction.BasicOps (normalForm, getModuleContents)

import Agda.Syntax.Common as Common
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Internal as I
import Agda.Syntax.Position (Range)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad

import Agda.TypeChecking.Conversion (equalType)
import Agda.TypeChecking.Free.Precompute (precomputedFreeVars)
import Agda.TypeChecking.MetaVars (newTelMeta)
import Agda.TypeChecking.Monad as TCM
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Impossible (impossible)
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Permutation
import Agda.Utils.VarSet as VarSet (null)

-- temporarily a tuple of name and type
type LemmingsResult = [(C.Name, Type)]

-- | Lemmings entry point for when running inside of an interaction point.
--   This simply gathers the goal type of the hole, gathers all names in scope,
--   and filters them by if they match the goal type according to Lemmings.
lemmings :: MonadTCM tcm
  => Rewrite
  -> InteractionId -- the hole to run on
  -> Range
  -> String
  -> tcm LemmingsResult
lemmings norm iid rng str = liftTCM $ do
  reportSDoc "lemmings.top" 10 (text "Running Lemmings on interaction point" <+> pretty iid)

  scope <- getInteractionScope iid
  let namesInScope = filter ((PatternSynName /=) . anameKind . snd)
                     $ List1.concat
                     $ map (\(c, as) -> fmap (c,) as)
                     $ Map.toList
                     $ (nsNames . everythingInScope) scope

  namesAndTypes <- forM namesInScope $ \(x, n) -> do
    t <- normalForm norm =<< typeOfConst (anameName n)
    return (x, t)

  reportSDoc "lemmings.top" 10 $ (text "Found ") <+> (text (show $ length namesInScope)) <+> (text " names")

  ip <- lookupInteractionPoint iid
  res <- case ipMeta ip of
    Nothing -> return []
    Just meta -> do
      goalType <- metaType meta
      reportSDoc "lemmings.top" 10 $ text "Comparing against goal type " <+> (pretty goalType)
      filterNames namesAndTypes goalType

  return res

-- | Filter a set of names and associated types to ones that match the
--   given goal type.
--
--   This is the crux of Lemmings.
filterNames :: LemmingsResult -> Type -> TCM LemmingsResult
filterNames ((nm, t) : xs) goal = do
  let split = (firstNoAbs t) - (firstNoAbs goal)
  reportSDoc "lemmings.top" 20 $ (text "Tele split point at ") <+> (pretty split)

  t' <- nonDepArgs t

  reportSDoc "lemmings.top" 20 $ (text "Checking ") <+> (pretty nm) <+> (text " : " ) <+> pretty t
  reportSDoc "lemmings.top" 30 $ (text "Type reordered: ") <+> (pretty $ t')

  match <- localTCState $ do
    tel <- telView t'
    let (head,_) = splitTelescopeAt split (theTel tel)
    args <- newTelMeta head
    core <- piApplyM t' args
    
    reportSDoc "lemmings.top" 20 $ (text "Comparison type: ") <+> (pretty core)
    
    checkType goal core
  
  reportSDoc "lemmings.top" 20 $ (text "Match?: ") <+> (pretty match)
  reportSDoc "lemmings.top" 20 $ (text " ")

  rest <- filterNames xs goal
  
  if (match)
    then return $ (nm,t) : rest
    else return rest

filterNames _ _ = return []

-- | pad a permutation up until the required length
--   Assumes that the maximum in the given list
--   equals the length of the list
padPerm :: Int -> [Int] -> [Int]
padPerm n ns = ns ++ (enumFromTo (length ns) n)

-- | Move all non-dependent implicits to head of Pi type
--   by applying the permutation given by `argPerm`
nonDepArgs :: Type -> TCM Type
nonDepArgs t@(El _ (Pi _ (Abs _ _))) = do
  tel <- telView t
  let tPerm = padPerm (length $ telToList $ theTel tel) (argPerm t)
  
  reportSDoc "lemmings.top" 30 $ (text "Permutation: ") <+> (pretty tPerm)
  
  let perm = (Perm (length tPerm) tPerm)
      telReordered = permuteTel perm (theTel tel)
      subst = renaming impossible (reverseP perm)
      core' = applySubst subst (theCore tel)
  
  return $ telePi telReordered core'
nonDepArgs t = return t

firstNoAbs :: Type -> Int
firstNoAbs = firstNoAbs' 0

firstNoAbs' :: Int -> Type -> Int
firstNoAbs' n (El sort (Pi dom (NoAbs name range))) = n
firstNoAbs' n (El sort (Pi dom (Abs name range))) = firstNoAbs' (n + 1) range
firstNoAbs' n _ = n

-- | Calculate a permutation of a given (Pi) type that results in all
--   non-dependent dependencies being moved to the head.
--
--   e.g. {a : Level} {A : Set a} {b : Level} {B : Set b} -> A -> B -> A becomes
--        {a b : Level} {A : Set a} {B : Set b} -> A -> B -> A
-- TODO: is there something better/cleaner than this nested pattern matching?
argPerm :: Type -> [Int]
argPerm (El sort (Pi dom (Abs name (El sort' (Pi dom' (Abs name' (El s'' (Pi d'' a''))))))))
    | VarSet.null $ precomputedFreeVars (unEl . unDom $ dom) = 0 : subPermsNoSwap
    | VarSet.null $ precomputedFreeVars (unEl . unDom $ dom') = insert 0
    | otherwise = 0 : subPermsNoSwap
  where
    subPerms :: [Int]
    subPerms = map (\n -> n + 1) $ argPerm (El sort' (Pi dom (Abs name (El s'' (Pi d'' a'')))))

    subPermsNoSwap :: [Int]
    subPermsNoSwap = map (\n -> n + 1) $ argPerm (El sort' (Pi dom' (Abs name' (El s'' (Pi d'' a'')))))

    insert :: Int -> [Int]
    insert n = case subPerms of
      (x : xs) -> x : n : xs
      []       -> n : []

argPerm _ = [0]

-- | Check if two types unify
checkType :: Type -> Type -> TCM Bool
checkType goal t = do
  equalType goal t
  return True
  `catchError` \err -> do
    return False
