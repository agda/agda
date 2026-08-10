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

import Data.Map qualified as Map
import Data.List as List

import Agda.Benchmarking qualified as Bench
import Agda.Syntax.Common
import Agda.Syntax.Info (pattern UnificationMeta)
import Agda.Syntax.Internal
import Agda.Syntax.Position (Range, noRange)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.Syntax.Translation.InternalToAbstract (reify, blankNotInScope)
import Agda.Syntax.Concrete.Name as Name
import Agda.Syntax.Builtin (BuiltinId)

import Agda.TypeChecking.CheckInternal ( checkInternal )
import Agda.TypeChecking.Conversion (equalType, compareType, leqType)
import Agda.TypeChecking.Empty (isEmptyType)
import Agda.TypeChecking.Implicit (implicitArgs)
import Agda.TypeChecking.Level (levelType)
import Agda.TypeChecking.MetaVars (newValueMeta, newTelMeta)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty as TCPretty
import Agda.TypeChecking.Primitive.Base (isBuiltin)
import Agda.TypeChecking.Reduce (reduce, instantiateFull, instantiate)
import Agda.TypeChecking.Rules.Term  (makeAbsurdLambda)
import Agda.TypeChecking.Rules.LHS.Unify.LeftInverse
import Agda.TypeChecking.Substitute (apply, theTel, theCore, applySubst)
import Agda.TypeChecking.Telescope

import Agda.Utils.Impossible
import Agda.Utils.List1 qualified as List1

import Agda.Interaction.Base (Rewrite(..))
import Agda.Interaction.BasicOps (normalForm, getModuleContents)

-- temporarily a tuple of name and type
type LemmingsResult = [(Name.Name, Type)]

{-
CURRENT DESIGN:
Normalise modulo isomorphisms
store in index tree (e.g. searchByPolyType paper):
  * Keep un-normalised type, module, and line number
  * Match all prefixes? I.e. to have A -> B -> C it is sufficient to have B -> C
Need some efficient encoding of the tree to store in file - cache!
Also need a standard location for said file, likely matching .agdai files
Probably worth keeping separate from .agdai files, in that it can be shipped separately for e.g.
web search?

-}

-- | Lemmings entry point for when running inside of an interaction point.
--   This simply gathers the goal type of the hole, gathers all names,
--   and filters them by if they match the goal type according to Lemmings.
lemmings :: MonadTCM tcm
  => Rewrite
  -> InteractionId -- the hole to run onn
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

  res <- forM namesInScope $ \(x, n) -> do
    t <- normalForm norm =<< typeOfConst (anameName n)
    return (x, t)

  reportSDoc "lemmings.top" 10 ((text "Found ") <+> (text (show $ length namesInScope)) <+> (text " names"))
  reportSDoc "lemmings.top" 10 $ text "Comparing against goal type..."

  ip <- lookupInteractionPoint iid
  res <- case ipMeta ip of
    Nothing -> return []
    Just meta -> do
      goalType <- metaType meta
      filterNames res goalType

  return res

hidingPred :: Hiding -> Bool
hidingPred Hidden = True
hidingPred _ = False

{-
Notes about implicit stuff:
- Slicing off implicits and replacing with metas is great for finding a more general type
  for a specific type, but not so much for finding a match *to* an already general type
- E.g., if our goal type itself has implicits, hard to tell which to chop off and replace with metas
  and which not to
- If you just replace all implicits with metas for goal type too, then less general types will match
  with more general types. E.g. if searching for A -> B -> A, then Nat -> Nat -> Nat will be
  considered a match
-}

-- | Filter a set of names and associated types to ones that match the
--   given goal type.
--
--   This is the crux of Lemmings.
filterNames :: LemmingsResult -> Type -> TCM LemmingsResult
filterNames ((nm, t) : xs) goal = do
  rest <- filterNames xs goal
  tele <- telView t

  reportSDoc "lemmings.top" 20 $ (text "Checking ") <+> (pretty nm) <+> (text " : " ) <+> pretty t

  matchNoImps <- localTCState $ do
    (args , core) <- implicitArgs (-1) hidingPred t

    reportSDoc "lemmings.top" 20 $ (text "Args: ") <+> (pretty args)
    reportSDoc "lemmings.top" 20 $ (text "Core: ") <+> (pretty core)
    
    checkType goal core

  matchImps <- checkType goal t
  let match = matchNoImps || matchImps

  reportSDoc "lemmings.top" 20 $ (text "Match?: ") <+> (pretty match)
  reportSDoc "lemmings.top" 20 $ (text " ")

  if (match)
    then return $ (nm,t) : rest
    else return rest

filterNames _ _ = return []


-- | Check if two types unify
checkType :: Type -> Type -> TCM Bool
checkType goal t = do
  equalType goal t
  return True
  `catchError` \err -> do
    return False
