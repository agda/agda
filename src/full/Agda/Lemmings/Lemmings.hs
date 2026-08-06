-- | Lemmings is the backbone of a new search tool for Agda
--   and is currently under-development.
--
--  Once complete, Lemmings will allow the user to gain a list of viable
--  lemmas or proofs that could be applied in some form to the current goal
--  and/or search for proofs/functions/datatypes in a similar fashion to
--  Hoogle
module Agda.Lemmings.Lemmings where

-- for now, steal possibly relevant imports from Mimer
import Prelude hiding (null)

import Control.Monad
import Control.Monad.Except (catchError)

import Data.Map qualified as Map
import Data.List as List

import qualified Agda.Benchmarking as Bench
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Info (pattern UnificationMeta)
import Agda.Syntax.Internal
import Agda.Syntax.Position (Range, noRange)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.Syntax.Translation.InternalToAbstract (reify, blankNotInScope)
import Agda.Syntax.Concrete.Name as Name
import Agda.Syntax.Common.Pretty as CPretty
import Agda.Syntax.Builtin (BuiltinId)

import Agda.TypeChecking.CheckInternal ( checkInternal )
import Agda.TypeChecking.Conversion (equalType, compareType, leqType)
import Agda.TypeChecking.Empty (isEmptyType)
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

-- entry point for running inside a hole
lemmings :: MonadTCM tcm
  => Rewrite
  -> InteractionId -- the hole to run onn
  -> Range
  -> String
  -> tcm LemmingsResult
lemmings norm iid rng str = liftTCM $ do
  reportSDoc "lemmings.top" 10 (TCPretty.text "Running Lemmings on interaction point" TCPretty.<+> TCPretty.pretty iid)

  -- NOTE: can probably use Mimer.Monad.getEverythinInScope, or at least a similar, cleaner implementation like it
  -- first we just want to get everything in scope
  scope <- getInteractionScope iid
  (modules, context, names) <- getModuleContents norm Nothing

  -- get a list of scopes from ScopeInfo and then extract names
  let scopeMods = Map.toList $ scope ^. scopeModules
  let names = map (\(mod, scope) -> (nsNames . allThingsInScope) scope) scopeMods

  -- took filtering from SearchAbout
  let namesInScope = concat
                     $ map (\snms -> filter ((PatternSynName /=) . anameKind . snd)
                     $ List1.concat
                     $ map (\(c, as) -> fmap (c,) as)
                     $ Map.toList snms) names

  -- get normalised types of all names in scope
  res <- forM namesInScope $ \(x, n) -> do
    t <- normalForm norm =<< typeOfConst (anameName n)
    return (x, t)

  -- NOTE: try filtering by if the types are an instance of the goal type
  --       and perhaps combine this with the ideas given by Reed
  --
  --       instance should be more general than equalType
  --       need to look into one unification function needs to be called to check this
  --
  --       but of course, this may be incredibly slow
  --
  --       ideas for after this: figure out a good way of indexing by instace/unification

  reportSDoc "lemmings.top" 10 ((TCPretty.text "Found ") TCPretty.<+> (TCPretty.text (show $ length namesInScope)) TCPretty.<+> (TCPretty.text " names"))

  reportSDoc "lemmings.top" 10 $ TCPretty.text "Comparing against goal type..."

  ip <- lookupInteractionPoint iid
  res <- case ipMeta ip of
    Nothing -> return []
    Just meta -> do
      goalType <- metaType meta
      goalTypeNorm <- normalForm Normalised goalType
      reportSDoc "lemmings.top" 10 $ (TCPretty.pretty goalTypeNorm)
      curryTerm (unEl goalTypeNorm)
      filterNames res goalType

  return res

{-
We start by grabbing absolutely everything in scope at the interaction point (Agda internal speak for a hole), which you can grab via`getInteractionScope`. We then grab all the types of the exported things from the scope (look at `getModuleContents` to see how to do this).

We then iterate over our list of names and types, and call `telView` to get our hands on all of the argument types. Underneath a call to `localTCState`, we then create metavariables for each of the argument types via `newTelMeta`, and then build a `Substitution` out of them via `termS`. Finally, we `applySubst` this substitution to the return type, and then unify the substituted type with our goal via `equalType` . If this unification succeeds, we record the lemma name and any metavariable solutions we have.

As a contrived example, consider the goal

? : Nat

and scope

const : {A  B : Set} -> A -> B -> A
not : Bool -> Bool

We'd start by calling `telView` on `const`, which would give us the list of types [Set, Set, x : @1, y : @1] and the type @3, where @n denotes the DeBruijn index n. Creating metas for this would give us a list [?0 : Set, ?1 : Set, ?2 : ?0, ?3 : ?2]. Applying that substitution to @3 gives us a return type of ?0. We then call equalType of this against the goal, which will succeed and solve ?0 as Nat. Our resulting telescope of metas is then [?1 : Set, ?2 : Nat, ?3 : ?2], which we store in the list.

On the other hand, going through the telView dance with not would give us a list of metavariables [?0 : Bool] and a return type of Bool, which would not unify with the goal.
-}

-- TODO: reporting names twice?
filterNames :: LemmingsResult -> Type -> TCM LemmingsResult
filterNames ((nm, t) : xs) goal = do
  rest <- filterNames xs goal
  tele <- telView t

  reportSDoc "lemmings.top" 20 $ (TCPretty.text "Checking ") TCPretty.<+> TCPretty.pretty t
  reportSDoc "lemmings.top" 20 $ (TCPretty.pretty nm)

  matchS <- localTCState $ do
    args <- newTelMeta $ theTel tele
    -- metas :: [Arg Term]
    let metas = map unArg args
        -- subs = termsS impossible metas

    reportSDoc "lemmings.top" 20 $ (TCPretty.text "Metas: ") TCPretty.<+> TCPretty.pretty metas
    -- reportSDoc "lemmings.top" 20 $ (TCPretty.text "Subs: ") TCPretty.<+> TCPretty.pretty subs

    -- return $ applySubst subs (theCore tele)
    tInst <- piApplyM t args

    reportSDoc "lemmings.top" 20 $ TCPretty.pretty tInst
    reportSDoc "lemmings.top" 20 $ TCPretty.text " "

    checkType goal tInst
  -- let isoTypes = generateIsoTypes t
  -- reportSDoc "lemmings.top" 20 $ TCPretty.pretty isoTypes

  -- matchT <- checkTypes goal (generateIsoTypes t)

  reportSDoc "lemmings.top" 20 $ (TCPretty.text "Match?: ") TCPretty.<+> (TCPretty.pretty matchS)
  reportSDoc "lemmings.top" 20 $ TCPretty.text " "

  if (matchS) then
    return $ (nm,t) : rest
  else
    return rest

filterNames _ _ = return []

-- TODO: implement
-- TODO: ugly!
-- | Generates a list of types that are isomorphic to the given type under common isomorphisms. Does not generate *all*
--   isomorphic types.
generateIsoTypes :: Type -> [Type]
generateIsoTypes t = case unEl t of
                       (Pi dom arg) -> t : (map (\term -> El {_getSort = _getSort t, unEl = term}) $ reorderArgs (unEl t))
                       _ -> [t]

-- TODO: ugly!
-- TODO: doesn't produce all reorderings
-- TODO: sort info being passed about is probably wrong
-- NOTE: seems to currently reorder non-dependent functions without implicit or instance arguments correctly
--       performance? god knows.
-- NOTE: for argument reordering, maybe converting both types to a canonical ordering is best? Rather than generating a list
--       for which may combinatorially explode on function types.... current way isn't a good idea tbh
reorderArgs :: Term -> [Term]
reorderArgs (Pi dom (NoAbs name argt)) = case (unEl argt) of
                                          (Pi dom' (NoAbs name' argt')) -> g ++ map (\term -> Pi dom' (NoAbs name' El {_getSort = _getSort argt, unEl = term})) (f : reorderArgs f)  where
                                            f = (Pi dom (NoAbs name argt'))
                                            g = map (\term -> (Pi dom (NoAbs name El {_getSort = _getSort argt', unEl = term}))) (reorderArgs (Pi dom' (NoAbs name' argt')))

                                            -- (Pi dom' (NoAbs name' El {_getSort = _getSort argt, unEl = (Pi dom (NoAbs name argt'))})) : []
                                          _ -> []
-- skip dependencies
reorderArgs (Pi dom (Abs name argt)) = map (\term -> (Pi dom (Abs name El {_getSort = _getSort argt, unEl = term}))) (reorderArgs $ unEl argt)
reorderArgs t = []

checkTypes :: Type -> [Type] -> TCM Bool
checkTypes _ [] = return False
checkTypes g (t:ts) = do
  check <- checkType g t
  if check then return check else checkTypes g ts

checkType :: Type -> Type -> TCM Bool
checkType goal t = do
  leqType goal t
  return True
  `catchError` \err -> do
    return False

-- TODO: implement
-- Normalises a type according to a set of isomorphisms
--   * All non-dependent arguments are sorted
--   * All dependencies via Pi are moved up until its bound variable isn't in free variables
--     and then sorted amongst other dependencies
--   * All products are curried
--   * etc
normIso :: Type -> TCM Type
normIso t = undefined

{-
Note: when unnormalised, qname for product is _x_
      when normalised, it goes to it's definition as a Sigma
-}
-- curry all products
-- Products are finite Pi
curryTerm :: Term -> TCM ()
curryTerm (Def qname elims) = do
  sigma <- isBuiltin qname BuiltinSigma
  reportSDoc "lemmings.top" 10 $ (TCPretty.text (show sigma))
  reportSDoc "lemmings.top" 10 $ (TCPretty.pretty qname)
  return ()
curryTerm (Pi dom (Abs name argt)) = curryTerm $ unEl argt
curryTerm (Pi dom (NoAbs name argt)) = curryTerm $ unEl argt
curryTerm t = return ()
