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

import Data.IntSet (null)

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
import Agda.TypeChecking.Substitute (apply, theTel, theCore, telePi)
import Agda.TypeChecking.Telescope

import Agda.Utils.Impossible
import Agda.Utils.List1 qualified as List1
import Agda.Utils.Permutation
import Agda.Utils.VarSet

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

Shorter types mainly work for non dependent functions? or atleast for tails without
dependencies

Say we have

(x : A) ... -> M -> N

and x not in FV(N)
then we can just have an N?

otherwise, need the x

Need function to exctract tail of Pi without free variables?

But would still miss nested Pi? e.g.

(x : A) ... -> M ... -> (y : B) -> N

and x not in FV(N) but y in FV(N)
then we could also just have (y : B) -> N

Many such cases
Could explode
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

Idea:
- If goal type contains no implicits in head, continue as normal
  otherwise, only slice off implicits until the arity is the same?
  Or, if goal type has bigger arity with implicits, ignore

Suppose we want

{A : Set} {B : Set} -> A -> B -> A

but of course, we have
const : {a : Level} {A : Set a} {B : Set a} -> A -> B -> A

we'd find that const has one more implicit and slice that off, replacing it with meta
variables:

{A : Set @0} {B : Set @1} -> A -> B -> A

which could then be unified with our goal type.

Again, if we want
Nat -> Nat -> Nat

Then all implicits would be cut off instead, giving
@1 -> @1 -> @3 (or something like that? idk deBruijin fully)

which would also unify

This generally works under the assumption that most implicit dependencies
whose purpose are to generalise a function (e.g. universe polymorphism)
will occur in the head of a function type

Reorder implicits? Must track dependencies, of course.

Move all non-dependent implicits to head?
Note: currentl problem seems constrained to examples, high likelihood I'm
thinking too much on something ultimately irrelevant

It would at least handle the case of universe polymorphism, which is good.
-}

-- | Filter a set of names and associated types to ones that match the
--   given goal type.
--
--   This is the crux of Lemmings.
filterNames :: LemmingsResult -> Type -> TCM LemmingsResult
filterNames ((nm, t) : xs) goal = do
  rest <- filterNames xs goal
  tele <- telView t

  goalImps <- countImplicits goal
  tImps <- countImplicits t

  -- if goal has no imps, then will slice all imps on type to check
  -- if goal has more imps, will just continue as normal
  let slice = tImps - goalImps

  reportSDoc "lemmings.top" 20 $ (text "Checking ") <+> (pretty nm) <+> (text " : " ) <+> pretty t

  reportSDoc "lemmings.top" 30 $ (text "Slicing off ") <+> (pretty slice) <+> (text " implicits")

  matchNoImps <- localTCState $ do
    (args , core) <- implicitArgs (-1) hidingPred t

    reportSDoc "lemmings.top" 20 $ (text "Args: ") <+> (pretty args)
    reportSDoc "lemmings.top" 20 $ (text "NonDep Imps: ") <+> (pretty $ nonDepArgs args)
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

-- | Move all non-dependent implicits to head of Pi type
--
-- ArgInfo contains list of free variables?
-- TODO: doesn't work
nonDepArgs :: Args -> Args
nonDepArgs (x:xs)
  | hasNoFree (argInfoFreeVariables . argInfo $ x) = x : nonDepArgs xs
  | otherwise = nonDepArgs xs
nonDepArgs _ = []

-- TODO: doesn't work
hasNoFree :: FreeVariables -> Bool
hasNoFree UnknownFVs = False
hasNoFree (KnownFVs set) = Agda.Utils.VarSet.null set

countImplicits :: Type -> TCM Int
countImplicits t = do
  (args , _) <- implicitArgs (-1) hidingPred t
  return $ length args

isImplicitAtHead :: Type -> TCM Bool
isImplicitAtHead t = do
  (args , _) <- implicitArgs (1) hidingPred t
  return $ (length args) > 0

-- | Check if two types unify
checkType :: Type -> Type -> TCM Bool
checkType goal t = do
  equalType goal t
  return True
  `catchError` \err -> do
    return False
