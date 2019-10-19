{-# LANGUAGE BangPatterns  #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies  #-}

{-|

This module implements the Agda Abstract Machine used for compile-time reduction. It's a
call-by-need environment machine with an implicit heap maintained using 'STRef's. See the 'AM' type
below for a description of the machine.

Some other tricks that improves performance:

- Memoise getConstInfo.

  A big chunk of the time during reduction is spent looking up definitions in the signature. Any
  long-running reduction will use only a handful definitions though, so memoising getConstInfo is a
  big win.

- Optimised case trees.

  Since we memoise getConstInfo we can do some preprocessing of the definitions, returning a
  'CompactDef' instead of a 'Definition'. In particular we streamline the case trees used for
  matching in a few ways:

    - Drop constructor arity information.
    - Use NameId instead of QName as map keys.
    - Special branch for natural number successor.

  None of these changes would make sense to incorporate into the actual case trees. The first two
  loses information that we need in other places and the third would complicate a lot of code
  working with case trees.

  'CompactDef' also has a special representation for built-in/primitive
  functions that can be implemented as pure functions from 'Literal's.

-}
module Agda.TypeChecking.Reduce.Fast
  ( fastReduce, fastNormalise ) where

import Control.Applicative hiding (empty)
import Control.Monad.ST
import Control.Monad.ST.Unsafe (unsafeSTToIO, unsafeInterleaveST)

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Traversable (traverse)
import Data.Semigroup ((<>))

import System.IO.Unsafe (unsafePerformIO)
import Data.IORef
import Data.STRef
import Data.Char

import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Literal

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Irrelevance (isPropM)
import Agda.TypeChecking.Monad hiding (Closure(..))
import Agda.TypeChecking.Reduce as R
import Agda.TypeChecking.Rewriting (rewrite)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Builtin hiding (constructorForm)

import Agda.Interaction.Options

import Agda.Utils.Float
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null (empty)
import Agda.Utils.Functor
import Agda.Utils.Pretty
import Agda.Utils.Size
import Agda.Utils.Zipper

import Agda.Utils.Impossible

import Debug.Trace

-- * Compact definitions

-- This is what the memoised getConstInfo returns. We essentially pick out only the
-- information needed for fast reduction from the definition.

data CompactDef =
  CompactDef { cdefDelayed        :: Bool
             , cdefNonterminating :: Bool
             , cdefUnconfirmed    :: Bool
             , cdefDef            :: CompactDefn
             , cdefRewriteRules   :: RewriteRules
             }

data CompactDefn
  = CFun  { cfunCompiled  :: FastCompiledClauses, cfunProjection :: Maybe QName }
  | CCon  { cconSrcCon :: ConHead, cconArity :: Int }
  | CForce   -- ^ primForce
  | CErase   -- ^ primErase
  | CTyCon   -- ^ Datatype or record type. Need to know this for primForce.
  | CAxiom   -- ^ Axiom or abstract defn
  | CPrimOp Int ([Literal] -> Term) (Maybe FastCompiledClauses)
            -- ^ Literals in reverse argument order
  | COther  -- ^ In this case we fall back to slow reduction

data BuiltinEnv = BuiltinEnv
  { bZero, bSuc, bTrue, bFalse, bRefl :: Maybe ConHead
  , bPrimForce, bPrimErase  :: Maybe QName }

-- | Compute a 'CompactDef' from a regular definition.
compactDef :: BuiltinEnv -> Definition -> RewriteRules -> ReduceM CompactDef
compactDef bEnv def rewr = do

  -- WARNING: don't use isPropM here because it relies on reduction,
  -- which causes an infinite loop.
  let isPrp = case getSort (defType def) of
        Prop{} -> True
        _      -> False
  let irr = isPrp || isIrrelevant (defArgInfo def)

  cdefn <-
    case theDef def of
      _ | irr -> pure CAxiom
      _ | Just (defName def) == bPrimForce bEnv   -> pure CForce
      _ | Just (defName def) == bPrimErase bEnv ->
          case telView' (defType def) of
            TelV tel _ | size tel == 5 -> pure CErase
                       | otherwise     -> pure COther
                          -- Non-standard equality. Fall back to slow reduce.
      Constructor{conSrcCon = c, conArity = n} -> pure CCon{cconSrcCon = c, cconArity = n}
      Function{funCompiled = Just cc, funClauses = _:_, funProjection = proj} ->
        pure CFun{ cfunCompiled   = fastCompiledClauses bEnv cc
                 , cfunProjection = projOrig <$> proj }
      Function{funClauses = []}      -> pure CAxiom
      Function{}                     -> pure COther -- Incomplete definition
      Datatype{dataClause = Nothing} -> pure CTyCon
      Record{recClause = Nothing}    -> pure CTyCon
      Datatype{}                     -> pure COther -- TODO
      Record{}                       -> pure COther -- TODO
      Axiom{}                        -> pure CAxiom
      DataOrRecSig{}                 -> pure CAxiom
      AbstractDefn{}                 -> pure CAxiom
      GeneralizableVar{}             -> __IMPOSSIBLE__
      Primitive{ primName = name, primCompiled = cc } ->
        case name of
          -- "primShowInteger" -- integers are not literals

          -- Natural numbers
          "primNatPlus"                -> mkPrim 2 $ natOp (+)
          "primNatMinus"               -> mkPrim 2 $ natOp (\ x y -> max 0 (x - y))
          "primNatTimes"               -> mkPrim 2 $ natOp (*)
          "primNatDivSucAux"           -> mkPrim 4 $ natOp4 divAux
          "primNatModSucAux"           -> mkPrim 4 $ natOp4 modAux
          "primNatLess"                -> mkPrim 2 $ natRel (<)
          "primNatEquality"            -> mkPrim 2 $ natRel (==)

          -- Word64
          "primWord64ToNat"            -> mkPrim 1 $ \ [LitWord64 _ a] -> nat (fromIntegral a)
          "primWord64FromNat"          -> mkPrim 1 $ \ [LitNat _ a]    -> word (fromIntegral a)

          -- Levels are not literals
          -- "primLevelZero"
          -- "primLevelSuc"
          -- "primLevelMax"

          -- Floats
          "primNatToFloat"             -> mkPrim 1 $ \ [LitNat _ a] -> float (fromIntegral a)
          "primFloatPlus"              -> mkPrim 2 $ floatOp (+)
          "primFloatMinus"             -> mkPrim 2 $ floatOp (-)
          "primFloatTimes"             -> mkPrim 2 $ floatOp (*)
          "primFloatNegate"            -> mkPrim 1 $ floatFun negate
          "primFloatDiv"               -> mkPrim 2 $ floatOp (/)
          "primFloatEquality"          -> mkPrim 2 $ floatRel floatEq
          "primFloatLess"              -> mkPrim 2 $ floatRel floatLt
          "primFloatNumericalEquality" -> mkPrim 2 $ floatRel (==)
          "primFloatNumericalLess"     -> mkPrim 2 $ floatRel (<)
          "primFloatSqrt"              -> mkPrim 1 $ floatFun sqrt
          -- "primRound"    -- Integers are not literals
          -- "primFloor"
          -- "primCeiling"
          "primExp"                    -> mkPrim 1 $ floatFun exp
          "primLog"                    -> mkPrim 1 $ floatFun log
          "primSin"                    -> mkPrim 1 $ floatFun sin
          "primCos"                    -> mkPrim 1 $ floatFun cos
          "primTan"                    -> mkPrim 1 $ floatFun tan
          "primASin"                   -> mkPrim 1 $ floatFun asin
          "primACos"                   -> mkPrim 1 $ floatFun acos
          "primATan"                   -> mkPrim 1 $ floatFun atan
          "primATan2"                  -> mkPrim 2 $ floatOp atan2
          "primShowFloat"              -> mkPrim 1 $ \ [LitFloat _ a] -> string (show a)

          -- Characters
          "primCharEquality"           -> mkPrim 2 $ charRel (==)
          "primIsLower"                -> mkPrim 1 $ charPred isLower
          "primIsDigit"                -> mkPrim 1 $ charPred isDigit
          "primIsAlpha"                -> mkPrim 1 $ charPred isAlpha
          "primIsSpace"                -> mkPrim 1 $ charPred isSpace
          "primIsAscii"                -> mkPrim 1 $ charPred isAscii
          "primIsLatin1"               -> mkPrim 1 $ charPred isLatin1
          "primIsPrint"                -> mkPrim 1 $ charPred isPrint
          "primIsHexDigit"             -> mkPrim 1 $ charPred isHexDigit
          "primToUpper"                -> mkPrim 1 $ charFun toUpper
          "primToLower"                -> mkPrim 1 $ charFun toLower
          "primCharToNat"              -> mkPrim 1 $ \ [LitChar _ a] -> nat (fromIntegral (fromEnum a))
          "primNatToChar"              -> mkPrim 1 $ \ [LitNat  _ a] -> char (toEnum $ fromIntegral $ a `mod` 0x110000)
          "primShowChar"               -> mkPrim 1 $ \ [a] -> string (prettyShow a)

          -- Strings
          -- "primStringToList"     -- We don't have the list builtins (but could have, TODO)
          -- "primStringFromList"   -- and they are not literals
          "primStringAppend"           -> mkPrim 2 $ \ [LitString _ a, LitString _ b] -> string (b ++ a)
          "primStringEquality"         -> mkPrim 2 $ \ [LitString _ a, LitString _ b] -> bool (b == a)
          "primShowString"             -> mkPrim 1 $ \ [a] -> string (prettyShow a)

          -- "primErase"
          -- "primForce"
          -- "primForceLemma"
          "primQNameEquality"          -> mkPrim 2 $ \ [LitQName _ a, LitQName _ b] -> bool (b == a)
          "primQNameLess"              -> mkPrim 2 $ \ [LitQName _ a, LitQName _ b] -> bool (b < a)
          "primShowQName"              -> mkPrim 1 $ \ [LitQName _ a] -> string (show a)
          -- "primQNameFixity"  -- We don't have fixity builtins (TODO)
          "primMetaEquality"           -> mkPrim 2 $ \ [LitMeta _ _ a, LitMeta _ _ b] -> bool (b == a)
          "primMetaLess"               -> mkPrim 2 $ \ [LitMeta _ _ a, LitMeta _ _ b] -> bool (b < a)
          "primShowMeta"               -> mkPrim 1 $ \ [LitMeta _ _ a] -> string (show (pretty a))

          _                            -> pure COther
        where
          fcc = fastCompiledClauses bEnv <$> cc
          mkPrim n op = pure $ CPrimOp n op fcc

          divAux k m n j = k + div (max 0 $ n + m - j) (m + 1)
          modAux k m n j | n > j     = mod (n - j - 1) (m + 1)
                         | otherwise = k + n

          ~(Just true)  = bTrue  bEnv <&> \ c -> Con c ConOSystem []
          ~(Just false) = bFalse bEnv <&> \ c -> Con c ConOSystem []

          bool   a = if a then true else false
          nat    a = Lit . LitNat    noRange $! a
          word   a = Lit . LitWord64 noRange $! a
          float  a = Lit . LitFloat  noRange $! a
          string a = Lit . LitString noRange $! a
          char   a = Lit . LitChar   noRange $! a

          -- Remember reverse order!
          natOp f [LitNat _ a, LitNat _ b] = nat (f b a)
          natOp _ _ = __IMPOSSIBLE__

          natOp4 f [LitNat _ a, LitNat _ b, LitNat _ c, LitNat _ d] = nat (f d c b a)
          natOp4 _ _ = __IMPOSSIBLE__

          natRel f [LitNat _ a, LitNat _ b] = bool (f b a)
          natRel _ _ = __IMPOSSIBLE__

          floatFun f [LitFloat _ a] = float (f a)
          floatFun _ _ = __IMPOSSIBLE__

          floatOp f [LitFloat _ a, LitFloat _ b] = float (f b a)
          floatOp _ _ = __IMPOSSIBLE__

          floatRel f [LitFloat _ a, LitFloat _ b] = bool (f b a)
          floatRel _ _ = __IMPOSSIBLE__

          charFun f [LitChar _ a] = char (f a)
          charFun _ _ = __IMPOSSIBLE__

          charPred f [LitChar _ a] = bool (f a)
          charPred _ _ = __IMPOSSIBLE__

          charRel f [LitChar _ a, LitChar _ b] = bool (f b a)
          charRel _ _ = __IMPOSSIBLE__

  return $
    CompactDef { cdefDelayed        = defDelayed def == Delayed
               , cdefNonterminating = defNonterminating def
               , cdefUnconfirmed    = defTerminationUnconfirmed def
               , cdefDef            = cdefn
               , cdefRewriteRules   = rewr
               }

-- Faster case trees ------------------------------------------------------

data FastCase c = FBranches
  { fprojPatterns   :: Bool
    -- ^ We are constructing a record here (copatterns).
    --   'conBranches' lists projections.
  , fconBranches    :: Map NameId c
    -- ^ Map from constructor (or projection) names to their arity
    --   and the case subtree.  (Projections have arity 0.)
  , fsucBranch      :: Maybe c
  , flitBranches    :: Map Literal c
    -- ^ Map from literal to case subtree.
  , fcatchAllBranch :: Maybe c
    -- ^ (Possibly additional) catch-all clause.
  , ffallThrough    :: Bool
    -- ^ (if True) In case of non-canonical argument use catchAllBranch.
  }

--UNUSED Liang-Ting Chen 2019-07-16
--noBranches :: FastCase a
--noBranches = FBranches{ fprojPatterns   = False
--                      , fconBranches    = Map.empty
--                      , fsucBranch      = Nothing
--                      , flitBranches    = Map.empty
--                      , fcatchAllBranch = Nothing
--                      , ffallThrough    = False }

-- | Case tree with bodies.

data FastCompiledClauses
  = FCase Int (FastCase FastCompiledClauses)
    -- ^ @Case n bs@ stands for a match on the @n@-th argument
    -- (counting from zero) with @bs@ as the case branches.
    -- If the @n@-th argument is a projection, we have only 'conBranches'
    -- with arity 0.
  | FEta Int [Arg QName] FastCompiledClauses (Maybe FastCompiledClauses)
    -- ^ Match on record constructor. Can still have a catch-all though. Just
    --   contains the fields, not the actual constructor.
  | FDone [Arg ArgName] Term
    -- ^ @Done xs b@ stands for the body @b@ where the @xs@ contains hiding
    --   and name suggestions for the free variables. This is needed to build
    --   lambdas on the right hand side for partial applications which can
    --   still reduce.
  | FFail
    -- ^ Absurd case.

fastCompiledClauses :: BuiltinEnv -> CompiledClauses -> FastCompiledClauses
fastCompiledClauses bEnv cc =
  case cc of
    Fail              -> FFail
    Done xs b         -> FDone xs b
    Case (Arg _ n) Branches{ etaBranch = Just (c, cc), catchAllBranch = ca } ->
      FEta n (conFields c) (fastCompiledClauses bEnv $ content cc) (fastCompiledClauses bEnv <$> ca)
    Case (Arg _ n) bs -> FCase n (fastCase bEnv bs)

fastCase :: BuiltinEnv -> Case CompiledClauses -> FastCase FastCompiledClauses
fastCase env (Branches proj con _ lit wild fT _) =
  FBranches
    { fprojPatterns   = proj
    , fconBranches    = Map.mapKeysMonotonic (nameId . qnameName) $ fmap (fastCompiledClauses env . content) (stripSuc con)
    , fsucBranch      = fmap (fastCompiledClauses env . content) $ flip Map.lookup con . conName =<< bSuc env
    , flitBranches    = fmap (fastCompiledClauses env) lit
    , ffallThrough    = fromMaybe False fT
    , fcatchAllBranch = fmap (fastCompiledClauses env) wild }
  where
    stripSuc | Just c <- bSuc env = Map.delete (conName c)
             | otherwise          = id


{-# INLINE lookupCon #-}
lookupCon :: QName -> FastCase c -> Maybe c
lookupCon c (FBranches _ cons _ _ _ _) = Map.lookup (nameId $ qnameName c) cons

-- QName memo -------------------------------------------------------------

{-# NOINLINE memoQName #-}
memoQName :: (QName -> a) -> (QName -> a)
memoQName f = unsafePerformIO $ do
  tbl <- newIORef Map.empty
  return (unsafePerformIO . f' tbl)
  where
    f' tbl x = do
      let i = nameId (qnameName x)
      m <- readIORef tbl
      case Map.lookup i m of
        Just y  -> return y
        Nothing -> do
          let y = f x
          writeIORef tbl (Map.insert i y m)
          return y

-- * Fast reduction

data Normalisation = WHNF | NF
  deriving (Eq)

data ReductionFlags = ReductionFlags
  { allowNonTerminating :: Bool
  , allowUnconfirmed    :: Bool
  , hasRewriting        :: Bool }

-- | The entry point to the reduction machine.
fastReduce :: Term -> ReduceM (Blocked Term)
fastReduce = fastReduce' WHNF

fastNormalise :: Term -> ReduceM Term
fastNormalise v = ignoreBlocking <$> fastReduce' NF v

fastReduce' :: Normalisation -> Term -> ReduceM (Blocked Term)
fastReduce' norm v = do
  let name (Con c _ _) = c
      name _         = __IMPOSSIBLE__
  zero  <- fmap name <$> getBuiltin' builtinZero
  suc   <- fmap name <$> getBuiltin' builtinSuc
  true  <- fmap name <$> getBuiltin' builtinTrue
  false <- fmap name <$> getBuiltin' builtinFalse
  refl  <- fmap name <$> getBuiltin' builtinRefl
  force <- fmap primFunName <$> getPrimitive' "primForce"
  erase <- fmap primFunName <$> getPrimitive' "primErase"
  let bEnv = BuiltinEnv { bZero = zero, bSuc = suc, bTrue = true, bFalse = false, bRefl = refl,
                          bPrimForce = force, bPrimErase = erase }
  allowedReductions <- asksTC envAllowedReductions
  rwr <- optRewriting <$> pragmaOptions
  constInfo <- unKleisli $ \f -> do
    info <- getConstInfo f
    rewr <- if rwr then instantiateRewriteRules =<< getRewriteRulesFor f
                   else return []
    compactDef bEnv info rewr
  let flags = ReductionFlags{ allowNonTerminating = NonTerminatingReductions `elem` allowedReductions
                            , allowUnconfirmed    = UnconfirmedReductions `elem` allowedReductions
                            , hasRewriting        = rwr }
  ReduceM $ \ redEnv -> reduceTm redEnv bEnv (memoQName constInfo) norm flags v

unKleisli :: (a -> ReduceM b) -> ReduceM (a -> b)
unKleisli f = ReduceM $ \ env x -> unReduceM (f x) env

-- * Closures

-- | The abstract machine represents terms as closures containing a 'Term', an environment, and a
--   spine of eliminations. Note that the environment doesn't necessarily bind all variables in the
--   term. The variables in the context in which the abstract machine is started are free in
--   closures. The 'IsValue' argument tracks whether the closure is in weak-head normal form.
data Closure s = Closure IsValue Term (Env s) (Spine s)
                 -- ^ The environment applies to the 'Term' argument. The spine contains closures
                 --   with their own environments.

-- | Used to track if a closure is @Unevaluated@ or a @Value@ (in weak-head normal form), and if so
--   why it cannot reduce further.
data IsValue = Value Blocked_ | Unevaled

-- | The spine is a list of eliminations. Application eliminations contain pointers.
type Spine s = [Elim' (Pointer s)]

isValue :: Closure s -> IsValue
isValue (Closure isV _ _ _) = isV

setIsValue :: IsValue -> Closure s -> Closure s
setIsValue isV (Closure _ t env spine) = Closure isV t env spine

-- | Apply a closure to a spine of eliminations. Note that this does not preserve the 'IsValue'
--   field.
clApply :: Closure s -> Spine s -> Closure s
clApply c [] = c
clApply (Closure _ t env es) es' = Closure Unevaled t env (es <> es')

-- | Apply a closure to a spine, preserving the 'IsValue' field. Use with care, since usually
--   eliminations do not preserve the value status.
clApply_ :: Closure s -> Spine s -> Closure s
clApply_ c [] = c
clApply_ (Closure b t env es) es' = Closure b t env (es <> es')

-- * Pointers and thunks

-- | Spines and environments contain pointers to closures to enable call-by-need evaluation.
data Pointer s = Pure (Closure s)
                 -- ^ Not a pointer. Used for closures that do not need to be shared to avoid
                 --   unnecessary updates.
               | Pointer {-# UNPACK #-} !(STPointer s)
                 -- ^ An actual pointer is an 'STRef' to a 'Thunk'. The thunk is set to 'BlackHole'
                 --   during the evaluation of its contents to make debugging loops easier.

type STPointer s = STRef s (Thunk (Closure s))

-- | A thunk is either a black hole or contains a value.
data Thunk a = BlackHole | Thunk a
  deriving (Functor)

derefPointer :: Pointer s -> ST s (Thunk (Closure s))
derefPointer (Pure x)      = return (Thunk x)
derefPointer (Pointer ptr) = readSTRef ptr

-- | In most cases pointers that we dereference do not contain black holes.
derefPointer_ :: Pointer s -> ST s (Closure s)
derefPointer_ ptr = do
  Thunk cl <- derefPointer ptr
  return cl

-- | Only use for debug printing!
unsafeDerefPointer :: Pointer s -> Thunk (Closure s)
unsafeDerefPointer (Pure x)    = Thunk x
unsafeDerefPointer (Pointer p) = unsafePerformIO (unsafeSTToIO (readSTRef p))

readPointer :: STPointer s -> ST s (Thunk (Closure s))
readPointer = readSTRef

storePointer :: STPointer s -> Closure s -> ST s ()
storePointer ptr !cl = writeSTRef ptr (Thunk cl)
    -- Note the strict match. To prevent leaking memory in case of unnecessary updates.

blackHole :: STPointer s -> ST s ()
blackHole ptr = writeSTRef ptr BlackHole

-- | Create a thunk. If the closure is a naked variable we can reuse the pointer from the
--   environment to avoid creating long pointer chains.
createThunk :: Closure s -> ST s (Pointer s)
createThunk (Closure _ (Var x []) env spine)
  | null spine, Just p <- lookupEnv x env = return p
createThunk cl = Pointer <$> newSTRef (Thunk cl)

-- | Create a thunk that is not shared or updated.
pureThunk :: Closure s -> Pointer s
pureThunk = Pure

-- * Environments

-- | The environment of a closure binds pointers to deBruijn indicies.
newtype Env s = Env [Pointer s]

emptyEnv :: Env s
emptyEnv = Env []
--UNUSED Liang-Ting Chen 2019-07-16
--isEmptyEnv :: Env s -> Bool
--isEmptyEnv (Env xs) = null xs

envSize :: Env s -> Int
envSize (Env xs) = length xs

envToList :: Env s -> [Pointer s]
envToList (Env xs) = xs

extendEnv :: Pointer s -> Env s -> Env s
extendEnv p (Env xs) = Env (p : xs)

-- | Unsafe.
lookupEnv_ :: Int -> Env s -> Pointer s
lookupEnv_ i (Env e) = indexWithDefault __IMPOSSIBLE__ e i

-- Andreas, 2018-11-12, which isn't this just Agda.Utils.List.!!! ?
lookupEnv :: Int -> Env s -> Maybe (Pointer s)
lookupEnv i e | i < n     = Just (lookupEnv_ i e)
              | otherwise = Nothing
  where n = envSize e

-- * The Agda Abstract Machine

-- | The abstract machine state has two states 'Eval' and 'Match' that determine what the machine is
--   currently working on: evaluating a closure in the Eval state and matching a spine against a
--   case tree in the Match state. Both states contain a 'ControlStack' of continuations for what to
--   do next. The heap is maintained implicitly using 'STRef's, hence the @s@ parameter.
data AM s = Eval (Closure s) !(ControlStack s)
            -- ^ Evaluate the given closure (the focus) to weak-head normal form. If the 'IsValue'
            --   field of the closure is 'Value' we look at the control stack for what to do. Being
            --   strict in the control stack is important! We can spend a lot of steps with
            --   unevaluated closures (where we update, but don't look at the control stack). For
            --   instance, long chains of 'suc' constructors.
          | Match QName FastCompiledClauses (Spine s) (MatchStack s) (ControlStack s)
            -- ^ @Match f cc spine stack ctrl@ Match the arguments @spine@ against the case tree
            --   @cc@. The match stack contains a (possibly empty) list of 'CatchAll' frames and a
            --   closure to return in case of a stuck match.

-- | The control stack contains a list of continuations, i.e. what to do with
--   the result of the current focus.
type ControlStack s = [ControlFrame s]

-- | The control stack for matching. Contains a list of CatchAllFrame's and the closure to return in
--   case of a stuck match.
data MatchStack s = [CatchAllFrame s] :> Closure s
infixr 2 :>, >:

(>:) :: CatchAllFrame s -> MatchStack s -> MatchStack s
(>:) c (cs :> cl) = c : cs :> cl
-- Previously written as:
--   c >: cs :> cl = c : cs :> cl
--
-- However, some versions/tools fail to parse infix data constructors properly.
-- For example, stylish-haskell@0.9.2.1 fails with the following error:
--   Language.Haskell.Stylish.Parse.parseModule: could not parse
--   src/full/Agda/TypeChecking/Reduce/Fast.hs: ParseFailed (SrcLoc
--   "<unknown>.hs" 625 1) "Parse error in pattern: "
--
-- See https://ghc.haskell.org/trac/ghc/ticket/10018 which may be related.

data CatchAllFrame s = CatchAll FastCompiledClauses (Spine s)
                        -- ^ @CatchAll cc spine@. Case trees are not fully expanded, that is,
                        --   inner matches can be partial and covered by a catch-all at a higher
                        --   level. This catch-all is represented on the match stack as a
                        --   @CatchAll@. @cc@ is the case tree in the catch-all case and @spine@ is
                        --   the value of the pattern variables at the point of the catch-all.

-- An Elim' with a hole.
data ElimZipper a = ApplyCxt ArgInfo
                  | IApplyType a a | IApplyFst a a | IApplySnd a a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Zipper (ElimZipper a) where
  type Carrier (ElimZipper a) = Elim' a
  type Element (ElimZipper a) = a

  firstHole (Apply arg)    = Just (unArg arg, ApplyCxt (argInfo arg))
  firstHole (IApply a x y) = Just (a, IApplyType x y)
  firstHole Proj{}         = Nothing

  plugHole x (ApplyCxt i)     = Apply (Arg i x)
  plugHole a (IApplyType x y) = IApply a x y
  plugHole x (IApplyFst a y)  = IApply a x y
  plugHole y (IApplySnd a x)  = IApply a x y

  nextHole a (IApplyType x y) = Right (x, IApplyFst a y)
  nextHole x (IApplyFst a y)  = Right (y, IApplySnd a x)
  nextHole y (IApplySnd a x)  = Left (IApply a x y)
  nextHole x c@ApplyCxt{}     = Left (plugHole x c)

-- | A spine with a single hole for a pointer.
type SpineContext s = ComposeZipper (ListZipper (Elim' (Pointer s)))
                                    (ElimZipper (Pointer s))

-- | Control frames are continuations that act on value closures.
data ControlFrame s = CaseK QName ArgInfo (FastCase FastCompiledClauses) (Spine s) (Spine s) (MatchStack s)
                        -- ^ @CaseK f i bs spine0 spine1 stack@. Pattern match on the focus (with
                        --   arg info @i@) using the @bs@ case tree. @f@ is the name of the function
                        --   doing the matching, and @spine0@ and @spine1@ are the values bound to
                        --   the pattern variables to the left and right (respectively) of the
                        --   focus. The match stack contains catch-all cases we need to consider if
                        --   this match fails.
                    | ArgK (Closure s) (SpineContext s)
                        -- ^ @ArgK cl cxt@. Used when computing full normal forms. The closure is
                        --   the head and the context is the spine with the current focus removed.
                    | NormaliseK
                        -- ^ Indicates that the focus should be evaluated to full normal form.
                    | ForceK QName (Spine s) (Spine s)
                        -- ^ @ForceK f spine0 spine1@. Evaluating @primForce@ of the focus. @f@ is
                        --   the name of @primForce@ and is used to build the result if evaluation
                        --   gets stuck. @spine0@ are the level and type arguments and @spine1@
                        --   contains (if not empty) the continuation and any additional
                        --   eliminations.
                    | EraseK QName (Spine s) (Spine s) (Spine s) (Spine s)
                        -- ^ @EraseK f spine0 spine1 spine2 spine3@. Evaluating @primErase@. The
                        --   first contains the level and type arguments. @spine1@ and @spine2@
                        --   contain at most one argument between them. If in @spine1@ it's the
                        --   value closure of the first argument to be compared and if in @spine2@
                        --   it's the unevaluated closure of the second argument.
                        --   @spine3@ contains the proof of equality we are erasing. It is passed
                        --   around but never actually inspected.
                    | NatSucK Integer
                        -- ^ @NatSucK n@. Add @n@ to the focus. If the focus computes to a natural
                        --   number literal this returns a new literal, otherwise it constructs @n@
                        --   calls to @suc@.
                    | PrimOpK QName ([Literal] -> Term) [Literal] [Pointer s] (Maybe FastCompiledClauses)
                        -- ^ @PrimOpK f op lits es cc@. Evaluate the primitive function @f@ using
                        --   the Haskell function @op@. @op@ gets a list of literal values in
                        --   reverse order for the arguments of @f@ and computes the result as a
                        --   term. The already computed arguments (in reverse order) are @lits@ and
                        --   @es@ are the arguments that should be computed after the current focus.
                        --   In case of built-in functions with corresponding Agda implementations,
                        --   @cc@ contains the case tree.
                    | UpdateThunk [STPointer s]
                        -- ^ @UpdateThunk ps@. Update the pointers @ps@ with the value of the
                        --   current focus.
                    | ApplyK (Spine s)
                        -- ^ @ApplyK spine@. Apply the current focus to the eliminations in @spine@.
                        --   This is used when a thunk needs to be updated with a partial
                        --   application of a function.

-- * Compilation and decoding

-- | The initial abstract machine state. Wrap the term to be evaluated in an empty closure. Note
--   that free variables of the term are treated as constants by the abstract machine. If computing
--   full normal form we start off the control stack with a 'NormaliseK' continuation.
compile :: Normalisation -> Term -> AM s
compile nf t = Eval (Closure Unevaled t emptyEnv []) [NormaliseK | nf == NF]

-- | The abstract machine treats uninstantiated meta-variables as blocked, but the rest of Agda does
--   not.
topMetaIsNotBlocked :: Blocked Term -> Blocked Term
topMetaIsNotBlocked (Blocked _ t@MetaV{}) = notBlocked t
topMetaIsNotBlocked b = b

decodePointer :: Pointer s -> ST s Term
decodePointer p = decodeClosure_ =<< derefPointer_ p

-- | Note: it's important to be lazy in the spine and environment when decoding. Hence the
--   'unsafeInterleaveST' here and in 'decodeEnv', and the special version of 'parallelS' in
--   'decodeClosure'.
decodeSpine :: Spine s -> ST s Elims
decodeSpine spine = unsafeInterleaveST $ (traverse . traverse) decodePointer spine

decodeEnv :: Env s -> ST s [Term]
decodeEnv env = unsafeInterleaveST $ traverse decodePointer (envToList env)

decodeClosure_ :: Closure s -> ST s Term
decodeClosure_ = ignoreBlocking <.> decodeClosure

-- | Turning an abstract machine closure back into a term. This happens in three cases:
--    * when reduction is finished and we return the weak-head normal term to the outside world.
--    * when the abstract machine encounters something it cannot handle and falls back to the slow
--      reduction engine
--    * when there are rewrite rules to apply
decodeClosure :: Closure s -> ST s (Blocked Term)
decodeClosure (Closure isV t env spine) = do
    vs <- decodeEnv env
    es <- decodeSpine spine
    return $ topMetaIsNotBlocked (applyE (applySubst (parS vs) t) es <$ b)
  where
    parS = foldr (:#) IdS  -- parallelS is too strict
    b    = case isV of
             Value b  -> b
             Unevaled -> notBlocked ()  -- only when falling back to slow reduce in which case the
                                        -- blocking tag is immediately discarded

-- | Turn a list of internal syntax eliminations into a spine. This builds closures and allocates
--   thunks for all the 'Apply' elims.
elimsToSpine :: Env s -> Elims -> ST s (Spine s)
elimsToSpine env es = do
    spine <- mapM thunk es
    forceSpine spine `seq` return spine
  where
    -- Need to be strict in mkClosure to avoid memory leak
    forceSpine = foldl (\ () -> forceEl) ()
    forceEl (Apply (Arg _ (Pure Closure{}))) = ()
    forceEl (Apply (Arg _ (Pointer{})))      = ()
    forceEl _                                = ()

    -- We don't preserve free variables of closures (in the sense of their
    -- decoding), since we freely add things to the spines.
    unknownFVs = setFreeVariables unknownFreeVariables

    thunk (Apply (Arg i t)) = Apply . Arg (unknownFVs i) <$> createThunk (closure (getFreeVariables i) t)
    thunk (Proj o f)        = return (Proj o f)
    thunk (IApply a x y)    = IApply <$> mkThunk a <*> mkThunk x <*> mkThunk y
      where mkThunk = createThunk . closure UnknownFVs

    -- Going straight for a value for literals is mostly to make debug traces
    -- less verbose and doesn't really buy anything performance-wise.
    closure _ t@Lit{} = Closure (Value $ notBlocked ()) t emptyEnv []
    closure fv t      = env' `seq` Closure Unevaled t env' []
      where env' = trimEnvironment fv env

-- | Trim unused entries from an environment. Currently only trims closed terms for performance
--   reasons.
trimEnvironment :: FreeVariables -> Env s -> Env s
trimEnvironment UnknownFVs env = env
trimEnvironment (KnownFVs fvs) env
  | IntSet.null fvs = emptyEnv
    -- Environment trimming is too expensive (costs 50% on some benchmarks), and while it does make
    -- some cases run in constant instead of linear space you need quite contrived examples to
    -- notice the effect.
  | otherwise       = env -- Env $ trim 0 $ envToList env
  where
    -- Important: strict enough that the trimming actually happens
    trim _ [] = []
    trim i (p : ps)
      | IntSet.member i fvs = (p :)             $! trim (i + 1) ps
      | otherwise           = (unusedPointer :) $! trim (i + 1) ps

-- | Build an environment for a body with some given free variables from a spine of arguments.
--   Returns a triple containing
--    * the left-over variable names (in case of partial application)
--    * the environment
--    * the remaining spine (in case of over-application)
buildEnv :: [Arg String] -> Spine s -> ([Arg String], Env s, Spine s)
buildEnv xs spine = go xs spine emptyEnv
  where
    go [] sp env = ([], env, sp)
    go xs0@(x : xs) sp env =
      case sp of
        []           -> (xs0, env, sp)
        Apply c : sp -> go xs sp (unArg c `extendEnv` env)
        IApply x y r : sp -> go xs sp (r `extendEnv` env)
        _            -> __IMPOSSIBLE__

unusedPointerString :: String
unusedPointerString = show (withFileAndLine Impossible)

unusedPointer :: Pointer s
unusedPointer = Pure (Closure (Value $ notBlocked ())
                     (Lit (LitString noRange unusedPointerString)) emptyEnv [])

-- * Running the abstract machine

-- | Evaluating a term in the abstract machine. It gets the type checking state and environment in
--   the 'ReduceEnv' argument, some precomputed built-in mappings in 'BuiltinEnv', the memoised
--   'getConstInfo' function, a couple of flags (allow non-terminating function unfolding, and
--   whether rewriting is enabled), and a term to reduce. The result is the weak-head normal form of
--   the term with an attached blocking tag.
reduceTm :: ReduceEnv -> BuiltinEnv -> (QName -> CompactDef) -> Normalisation -> ReductionFlags -> Term -> Blocked Term
reduceTm rEnv bEnv !constInfo normalisation ReductionFlags{..} =
    compileAndRun . traceDoc "-- fast reduce --"
  where
    -- Helpers to get information from the ReduceEnv.
    metaStore      = redSt rEnv ^. stMetaStore
    -- Are we currently instance searching. In that case we don't fail hard on missing clauses. This
    -- is a (very unsatisfactory) work-around for #3870.
    speculative    = redSt rEnv ^. stConsideringInstance
    getMeta m      = maybe __IMPOSSIBLE__ mvInstantiation (IntMap.lookup (metaId m) metaStore)
    partialDefs    = runReduce getPartialDefs
    rewriteRules f = cdefRewriteRules (constInfo f)
    callByNeed     = envCallByNeed (redEnv rEnv)
    iview          = runReduce intervalView'

    runReduce :: ReduceM a -> a
    runReduce m = unReduceM m rEnv

    -- Debug output. Taking care that we only look at the verbosity level once.
    hasVerb tag lvl = unReduceM (hasVerbosity tag lvl) rEnv
    doDebug = hasVerb "tc.reduce.fast" 110
    traceDoc :: Doc -> a -> a
    traceDoc
      | doDebug   = trace . show
      | otherwise = const id

    -- Checking for built-in zero and suc
    BuiltinEnv{ bZero = zero, bSuc = suc, bRefl = refl0 } = bEnv
    conNameId = nameId . qnameName . conName
    isZero = case zero of
               Nothing -> const False
               Just z  -> (conNameId z ==) . conNameId
    isSuc  = case suc of
               Nothing -> const False
               Just s  -> (conNameId s ==) . conNameId

    -- If there's a non-standard equality (for instance doubly-indexed) we fall back to slow reduce
    -- for primErase and "unbind" refl.
    refl = refl0 >>= \ c -> if cconArity (cdefDef $ constInfo $ conName c) == 0
                            then Just c else Nothing

    -- The entry point of the machine.
    compileAndRun :: Term -> Blocked Term
    compileAndRun t = runST (runAM (compile normalisation t))

    -- Run the machine in a given state. Prints the state if the right verbosity level is active.
    runAM :: AM s -> ST s (Blocked Term)
    runAM = if doDebug then \ s -> trace (prettyShow s) (runAM' s)
                       else runAM'

    -- The main function. This is where the stuff happens!
    runAM' :: AM s -> ST s (Blocked Term)

    -- Base case: The focus is a value closure and the control stack is empty. Decode and return.
    runAM' (Eval cl@(Closure Value{} _ _ _) []) = decodeClosure cl

    -- Unevaluated closure: inspect the term and take the appropriate action. For instance,
    --  - Change to the 'Match' state if a definition
    --  - Look up in the environment if variable
    --  - Perform a beta step if lambda and application elimination in the spine
    --  - Perform a record beta step if record constructor and projection elimination in the spine
    runAM' s@(Eval cl@(Closure Unevaled t env spine) !ctrl) = {-# SCC "runAM.Eval" #-}
      case t of

        -- Case: definition. Enter 'Match' state if defined function or shift to evaluating an
        -- argument and pushing the appropriate control frame for primitive functions. Fall back to
        -- slow reduce for unsupported definitions.
        Def f [] ->
          evalIApplyAM spine ctrl $
          let CompactDef{ cdefDelayed        = delayed
                        , cdefNonterminating = nonterm
                        , cdefUnconfirmed    = unconf
                        , cdefDef            = def } = constInfo f
              dontUnfold = (nonterm && not allowNonTerminating) ||
                           (unconf  && not allowUnconfirmed)    ||
                           (delayed && not (unfoldDelayed ctrl))
          in case def of
            CFun{ cfunCompiled = cc }
              | dontUnfold -> rewriteAM done
              | otherwise  -> runAM (Match f cc spine ([] :> cl) ctrl)
            CAxiom         -> rewriteAM done
            CTyCon         -> rewriteAM done
            CCon{}         -> runAM done   -- Only happens for builtinSharp (which is a Def when you bind it)
            CForce | (spine0, Apply v : spine1) <- splitAt 4 spine ->
              evalPointerAM (unArg v) [] (ForceK f spine0 spine1 : ctrl)
            CForce -> runAM done -- partially applied
            CErase | (spine0, Apply v : spine1 : spine2) <- splitAt 2 spine ->
              evalPointerAM (unArg v) [] (EraseK f spine0 [] [spine1] spine2 : ctrl)
            CErase -> runAM done -- partially applied
            CPrimOp n op cc | length spine == n,                      -- PrimOps can't be over-applied. They don't
                              Just (v : vs) <- allApplyElims spine -> -- return functions or records.
              evalPointerAM (unArg v) [] (PrimOpK f op [] (map unArg vs) cc : ctrl)
            CPrimOp{} -> runAM done  -- partially applied
            COther    -> fallbackAM s

        -- Case: zero. Return value closure with literal 0.
        Con c i [] | isZero c ->
          runAM (evalTrueValue (Lit (LitNat noRange 0)) emptyEnv spine ctrl)

        -- Case: suc. Suc is strict in its argument to make sure we return a literal whenever
        -- possible. Push a 'NatSucK' frame on the control stack and evaluate the argument.
        Con c i [] | isSuc c, Apply v : _ <- spine ->
          evalPointerAM (unArg v) [] (sucCtrl ctrl)

        -- Case: constructor. Perform beta reduction if projected from, otherwise return a value.
        Con c i []
          -- Constructors of types in Prop are not representex as
          -- CCon, so this match might fail!
          | CCon{cconSrcCon = c', cconArity = ar} <- cdefDef (constInfo (conName c)) ->
            evalIApplyAM spine ctrl $
            case splitAt ar spine of
              (args, Proj _ p : spine')
                  -> evalPointerAM (unArg arg) spine' ctrl  -- Andreas #2170: fit argToDontCare here?!
                where
                  fields    = map unArg $ conFields c
                  Just n    = List.elemIndex p fields
                  Apply arg = args !! n
              _ -> rewriteAM (evalTrueValue (Con c' i []) env spine ctrl)
          | otherwise -> runAM done

        -- Case: variable. Look up the variable in the environment and evaluate the resulting
        -- pointer. If the variable is not in the environment it's a free variable and we adjust the
        -- deBruijn index appropriately.
        Var x []   ->
          evalIApplyAM spine ctrl $
          case lookupEnv x env of
            Nothing -> runAM (evalValue (notBlocked ()) (Var (x - envSize env) []) emptyEnv spine ctrl)
            Just p  -> evalPointerAM p spine ctrl

        -- Case: lambda. Perform the beta reduction if applied. Otherwise it's a value.
        Lam h b ->
          case spine of
            [] -> runAM done
            elim : spine' ->
              case b of
                Abs   _ b -> runAM (evalClosure b (getArg elim `extendEnv` env) spine' ctrl)
                NoAbs _ b -> runAM (evalClosure b env spine' ctrl)
          where
            getArg (Apply v)      = unArg v
            getArg (IApply _ _ v) = v
            getArg Proj{}         = __IMPOSSIBLE__

        -- Case: values. Literals and function types are already in weak-head normal form.
        -- We throw away the environment for literals mostly to make debug printing less verbose.
        -- And we know the spine is empty since literals cannot be applied or projected.
        Lit{} -> runAM (evalTrueValue t emptyEnv [] ctrl)
        Pi{}  -> runAM done
        DontCare{} -> runAM done

        -- Case: non-empty spine. If the focused term has a non-empty spine, we shift the
        -- eliminations onto the spine.
        Def f   es -> shiftElims (Def f   []) emptyEnv env es
        Con c i es -> shiftElims (Con c i []) emptyEnv env es
        Var x   es -> shiftElims (Var x   []) env      env es

        -- Case: metavariable. If it's instantiated evaluate the value. Meta instantiations are open
        -- terms with a specified list of free variables. buildEnv constructs the appropriate
        -- environment for the closure. Avoiding shifting spines for open metas
        -- save a bit of performance.
        MetaV m es -> evalIApplyAM spine ctrl $
          case getMeta m of
            InstV xs t -> do
              spine' <- elimsToSpine env es
              let (zs, env, !spine'') = buildEnv xs (spine' <> spine)
              runAM (evalClosure (lams zs t) env spine'' ctrl)
            _ -> runAM (Eval (mkValue (blocked m ()) cl) ctrl)

        -- Case: unsupported. These terms are not handled by the abstract machine, so we fall back
        -- to slowReduceTerm for these.
        Level{}    -> fallbackAM s
        Sort{}     -> fallbackAM s
        Dummy{}    -> fallbackAM s

      where done = Eval (mkValue (notBlocked ()) cl) ctrl
            shiftElims t env0 env es = do
              spine' <- elimsToSpine env es
              runAM (evalClosure t env0 (spine' <> spine) ctrl)

    -- If the current focus is a value closure, we look at the control stack.

    -- Case NormaliseK: The focus is a weak-head value that should be fully normalised.
    runAM' s@(Eval cl@(Closure b t env spine) (NormaliseK : ctrl)) =
      case t of
        Def _   [] -> normaliseArgsAM (Closure b t emptyEnv []) spine ctrl
        Con _ _ [] -> normaliseArgsAM (Closure b t emptyEnv []) spine ctrl
        Var _   [] -> normaliseArgsAM (Closure b t emptyEnv []) spine ctrl
        MetaV _ [] -> normaliseArgsAM (Closure b t emptyEnv []) spine ctrl

        Lit{} -> runAM done

        -- We might get these from fallbackAM
        Def f   es -> shiftElims (Def f   []) emptyEnv env es
        Con c i es -> shiftElims (Con c i []) emptyEnv env es
        Var x   es -> shiftElims (Var x   []) env      env es
        MetaV m es -> shiftElims (MetaV m []) emptyEnv env es

        _ -> fallbackAM s -- fallbackAM knows about NormaliseK

      where done = Eval (mkValue (notBlocked ()) cl) ctrl
            shiftElims t env0 env es = do
              spine' <- elimsToSpine env es
              runAM (Eval (Closure b t env0 (spine' <> spine)) (NormaliseK : ctrl))

    -- Case: ArgK: We successfully normalised an argument. Start on the next argument, or if there
    -- isn't one we're done.
    runAM' (Eval cl (ArgK cl0 cxt : ctrl)) =
      case nextHole (pureThunk cl) cxt of
        Left spine      -> runAM (Eval (clApply_ cl0 spine) ctrl)
        Right (p, cxt') -> evalPointerAM p [] (NormaliseK : ArgK cl0 cxt' : ctrl)

    -- Case: NatSucK m

    -- If literal add m to the literal,
    runAM' (Eval cl@(Closure Value{} (Lit (LitNat r n)) _ _) (NatSucK m : ctrl)) =
      runAM (evalTrueValue (Lit $! LitNat r $! m + n) emptyEnv [] ctrl)

    -- otherwise apply 'suc' m times.
    runAM' (Eval cl (NatSucK m : ctrl)) =
        runAM (Eval (mkValue (notBlocked ()) $ plus m cl) ctrl)
      where
        plus 0 cl = cl
        plus n cl =
          trueValue (Con (fromMaybe __IMPOSSIBLE__ suc) ConOSystem []) emptyEnv $
                     Apply (defaultArg arg) : []
          where arg = pureThunk (plus (n - 1) cl)

    -- Case: PrimOpK

    -- If literal apply the primitive function if no more arguments, otherwise
    -- store the literal in the continuation and evaluate the next argument.
    runAM' (Eval (Closure _ (Lit a) _ _) (PrimOpK f op vs es cc : ctrl)) =
      case es of
        []      -> runAM (evalTrueValue (op (a : vs)) emptyEnv [] ctrl)
        e : es' -> evalPointerAM e [] (PrimOpK f op (a : vs) es' cc : ctrl)

    -- If not a literal we use the case tree if there is one, otherwise we are stuck.
    runAM' (Eval cl@(Closure (Value blk) _ _ _) (PrimOpK f _ vs es mcc : ctrl)) =
      case mcc of
        Nothing -> rewriteAM (Eval stuck ctrl)
        Just cc -> runAM (Match f cc spine ([] :> notstuck) ctrl)
      where
        p         = pureThunk cl
        lits      = map (pureThunk . litClos) (reverse vs)
        spine     = fmap (Apply . defaultArg) $ lits <> [p] <> es
        stuck     = Closure (Value blk) (Def f []) emptyEnv spine
        notstuck  = Closure Unevaled    (Def f []) emptyEnv spine
        litClos l = trueValue (Lit l) emptyEnv []

    -- Case: ForceK. Here we need to check if the argument is a canonical form (i.e. not a variable
    -- or stuck function call) and if so apply the function argument to the value. If it's not
    -- canonical we are stuck.
    runAM' (Eval arg@(Closure (Value blk) t _ _) (ForceK pf spine0 spine1 : ctrl))
      | isCanonical t =
        case spine1 of
          Apply k : spine' ->
            evalPointerAM (unArg k) (elim : spine') ctrl
          [] -> -- Partial application of primForce to canonical argument, return λ k → k arg.
            runAM (evalTrueValue (lam (defaultArg "k") $ Var 0 [Apply $ defaultArg $ Var 1 []])
                                 (argPtr `extendEnv` emptyEnv) [] ctrl)
          _ -> __IMPOSSIBLE__
      | otherwise = rewriteAM (Eval stuck ctrl)
      where
        argPtr = pureThunk arg
        elim   = Apply (defaultArg argPtr)
        spine' = spine0 <> [elim] <> spine1
        stuck  = Closure (Value blk) (Def pf []) emptyEnv spine'

        isCanonical u = case u of
          Lit{}      -> True
          Con{}      -> True
          Lam{}      -> True
          Pi{}       -> True
          Sort{}     -> True
          Level{}    -> True
          DontCare{} -> True
          Dummy{}    -> False
          MetaV{}    -> False
          Var{}      -> False
          Def q _  -- Type constructors (data/record) are considered canonical for 'primForce'.
            | CTyCon <- cdefDef (constInfo q) -> True
            | otherwise                       -> False

    -- Case: EraseK. We evaluate both arguments to values, then do a simple check for the easy
    -- cases and otherwise fall back to slow reduce.
    runAM' (Eval cl2@(Closure Value{} arg2 _ _) (EraseK f spine0 [Apply p1] _ spine3 : ctrl)) = do
      cl1@(Closure _ arg1 _ sp1) <- derefPointer_ (unArg p1)
      case (arg1, arg2) of
        (Lit l1, Lit l2) | l1 == l2, isJust refl ->
          runAM (evalTrueValue (Con (fromJust refl) ConOSystem []) emptyEnv [] ctrl)
        _ ->
          let spine = spine0 ++ map (Apply . hide . defaultArg . pureThunk) [cl1, cl2] ++ spine3 in
          fallbackAM (evalClosure (Def f []) emptyEnv spine ctrl)
    runAM' (Eval cl1@(Closure Value{} _ _ _) (EraseK f spine0 [] [Apply p2] spine3 : ctrl)) =
      evalPointerAM (unArg p2) [] (EraseK f spine0 [Apply $ hide $ defaultArg $ pureThunk cl1] [] spine3 : ctrl)
    runAM' (Eval _ (EraseK{} : _)) =
      __IMPOSSIBLE__

    -- Case: UpdateThunk. Write the value to the pointers in the UpdateThunk frame.
    runAM' (Eval cl@(Closure Value{} _ _ _) (UpdateThunk ps : ctrl)) =
      mapM_ (`storePointer` cl) ps >> runAM (Eval cl ctrl)

    -- Case: ApplyK. Application after thunk update. Add the spine from the control frame to the
    -- closure.
    runAM' (Eval cl@(Closure Value{} _ _ _) (ApplyK spine : ctrl)) =
      runAM (Eval (clApply cl spine) ctrl)

    -- Case: CaseK. Pattern matching against a value. If it's a stuck value the pattern match is
    -- stuck and we return the closure from the match stack (see stuckMatch). Otherwise we need to
    -- find a matching branch switch to the Match state. If there is no matching branch we look for
    -- a CatchAll in the match stack, or fail if there isn't one (see failedMatch). If the current
    -- branches contain a catch-all case we need to push a CatchAll on the match stack if picking
    -- one of the other branches.
    runAM' (Eval cl@(Closure (Value blk) t env spine) ctrl0@(CaseK f i bs spine0 spine1 stack : ctrl)) =
      {-# SCC "runAM.CaseK" #-}
      case blk of
        Blocked{} | null [()|Con{} <- [t]] -> stuck -- we might as well check the blocking tag first
        _ -> case t of
          -- Case: suc constructor
          Con c ci [] | isSuc c -> matchSuc $ matchCatchall $ failedMatch f stack ctrl

          -- Case: constructor
          Con c ci [] -> matchCon c ci (length spine) $ matchCatchall $ failedMatch f stack ctrl

          -- Case: non-empty elims. We can get here from a fallback (which builds a value without
          -- shifting arguments onto spine)
          Con c ci es -> do
            spine' <- elimsToSpine env es
            runAM (evalValue blk (Con c ci []) emptyEnv (spine' <> spine) ctrl0)
          -- Case: natural number literals. Literal natural number patterns are translated to
          -- suc-matches, so there is no need to try matchLit.
          Lit (LitNat _ 0) -> matchLitZero  $ matchCatchall $ failedMatch f stack ctrl
          Lit (LitNat _ n) -> matchLitSuc n $ matchCatchall $ failedMatch f stack ctrl

          -- Case: literal
          Lit l -> matchLit l $ matchCatchall $ failedMatch f stack ctrl

          -- Case: hcomp
          Def q [] | isJust $ lookupCon q bs -> matchCon' q (length spine) $ matchCatchall $ failedMatch f stack ctrl
          Def q es | isJust $ lookupCon q bs -> do
            spine' <- elimsToSpine env es
            runAM (evalValue blk (Def q []) emptyEnv (spine' <> spine) ctrl0)

          -- Case: not constructor or literal. In this case we are stuck.
          _ -> stuck
      where
        -- If ffallThrough is set we take the catch-all (if any) rather than being stuck. I think
        -- this happens for partial functions with --cubical (@saizan: is this true?).
        stuck | ffallThrough bs = matchCatchall reallyStuck
              | otherwise       = reallyStuck

        reallyStuck = do
            -- Compute new reason for being stuck. See Agda.Syntax.Internal.stuckOn for the logic.
            blk' <- case blk of
                      Blocked{}      -> return blk
                      NotBlocked r _ -> decodeClosure_ cl <&> \ v -> NotBlocked (stuckOn (Apply $ Arg i v) r) ()
            stuckMatch blk' stack ctrl

        -- This the spine at this point in the matching. A catch-all match doesn't change the spine.
        catchallSpine = spine0 <> [Apply $ Arg i p] <> spine1
          where p = pureThunk cl -- cl is already a value so no need to thunk it.

        -- Push catch-all frame on the match stack if there is a catch-all (and we're not taking it
        -- right now).
        catchallStack = case fcatchAllBranch bs of
          Nothing -> stack
          Just cc -> CatchAll cc catchallSpine >: stack

        -- The matchX functions below all take an extra argument which is what to do if there is no
        -- appropriate branch in the case tree. ifJust is maybe with a different argument order
        -- letting you chain a bunch if maybe matches in if-then-elseif fashion.
        (m `ifJust` f) z = maybe z f m

        -- Matching constructor: Switch to the Match state, inserting the constructor arguments in
        -- the spine between spine0 and spine1.
        matchCon c ci ar = matchCon' (conName c) ar
        matchCon' q ar = lookupCon q bs `ifJust` \ cc ->
          runAM (Match f cc (spine0 <> spine <> spine1) catchallStack ctrl)

        -- Catch-all: Don't add a CatchAll to the match stack since this _is_ the catch-all.
        matchCatchall = fcatchAllBranch bs `ifJust` \ cc ->
          runAM (Match f cc catchallSpine stack ctrl)

        -- Matching literal: Switch to the Match state. There are no arguments to add to the spine.
        matchLit l = Map.lookup l (flitBranches bs) `ifJust` \ cc ->
          runAM (Match f cc (spine0 <> spine1) catchallStack ctrl)

        -- Matching a 'suc' constructor: Insert the argument in the spine.
        matchSuc = fsucBranch bs `ifJust` \ cc ->
            runAM (Match f cc (spine0 <> spine <> spine1) catchallStack ctrl)

        -- Matching a non-zero natural number literal: Subtract one from the literal and
        -- insert it in the spine for the Match state.
        matchLitSuc n = fsucBranch bs `ifJust` \ cc ->
            runAM (Match f cc (spine0 <> [Apply $ defaultArg arg] <> spine1) catchallStack ctrl)
          where n'  = n - 1
                arg = pureThunk $ trueValue (Lit $ LitNat noRange n') emptyEnv []

        -- Matching a literal 0. Simply calls matchCon with the zero constructor.
        matchLitZero = matchCon (fromMaybe __IMPOSSIBLE__ zero) ConOSystem 0
                            -- If we have a nat literal we have builtin zero.

    -- Case: Match state. Here we look at the case tree and take the appropriate action:
    --   - FFail: stuck
    --   - FDone: evaluate body
    --   - FEta: eta expand argument
    --   - FCase on projection: pick corresponding branch and keep matching
    --   - FCase on argument: push CaseK frame on control stack and evaluate argument
    runAM' (Match f cc spine stack ctrl) = {-# SCC "runAM.Match" #-}
      case cc of
        -- Absurd match. You can get here for open terms.
        FFail -> stuckMatch (NotBlocked AbsurdMatch ()) stack ctrl

        -- Matching complete. Compute the environment for the body and switch to the Eval state.
        FDone xs body -> do
            -- Don't ask me why, but not being strict in the spine causes a memory leak.
            let (zs, env, !spine') = buildEnv xs spine
            runAM (Eval (Closure Unevaled (lams zs body) env spine') ctrl)

        -- A record pattern match. This does not block evaluation (since that would violate eta
        -- equality), so in this case we replace the argument with its projections in the spine and
        -- keep matching.
        FEta n fs cc ca ->
          case splitAt n spine of                           -- Question: add lambda here? doesn't
            (_, [])                    -> done Underapplied -- matter for equality, but might for
            (spine0, Apply e : spine1) -> do                -- rewriting or 'with'.
              -- Replace e by its projections in the spine. And don't forget a
              -- CatchAll frame if there's a catch-all.
              let projClosure (Arg ai f) = Closure Unevaled (Var 0 []) (extendEnv (unArg e) emptyEnv) [Proj ProjSystem f]
              projs <- mapM (createThunk . projClosure) fs
              let spine' = spine0 <> map (Apply . defaultArg) projs <> spine1
                  stack' = caseMaybe ca stack $ \ cc -> CatchAll cc spine >: stack
              runAM (Match f cc spine' stack' ctrl)
            _ -> __IMPOSSIBLE__

        -- Split on nth elimination in the spine. Can be either a regular split or a copattern
        -- split.
        FCase n bs ->
          case splitAt n spine of
            -- If the nth elimination is not given, we're stuck.
            (_, []) -> done Underapplied
            -- Apply elim: push the current match on the control stack and evaluate the argument
            (spine0, Apply e : spine1) ->
              evalPointerAM (unArg e) [] $ CaseK f (argInfo e) bs spine0 spine1 stack : ctrl
            -- Projection elim: in this case we must be in a copattern split and find the projection
            -- in the case tree and keep going. If it's not there it might be because it's not the
            -- original projection (issue #2265). If so look up the original projection instead.
            -- That _really_ should be there since copattern splits cannot be partial. Except of
            -- course, the user might still have written a partial function so we should check
            -- partialDefs before throwing an impossible (#3012).
            (spine0, Proj o p : spine1) ->
              case lookupCon p bs <|> ((`lookupCon` bs) =<< op) of
                Nothing
                  | f `elem` partialDefs -> stuckMatch (NotBlocked MissingClauses ()) stack ctrl
                  | otherwise          -> __IMPOSSIBLE__
                Just cc -> runAM (Match f cc (spine0 <> spine1) stack ctrl)
              where CFun{ cfunProjection = op } = cdefDef (constInfo p)
            (_, IApply{} : _) -> __IMPOSSIBLE__ -- Paths cannot be defined by pattern matching
      where done why = stuckMatch (NotBlocked why ()) stack ctrl

    -- 'evalPointerAM p spine ctrl'. Evaluate the closure pointed to by 'p' applied to 'spine' with
    -- the control stack 'ctrl'. If 'p' points to an unevaluated thunk, a 'BlackHole' is written to
    -- the pointer and an 'UpdateThunk' frame is pushed to the control stack. In this case the
    -- application to the spine has to be deferred until after the update through an 'ApplyK' frame.
    evalPointerAM :: Pointer s -> Spine s -> ControlStack s -> ST s (Blocked Term)
    evalPointerAM (Pure cl)   spine ctrl = runAM (Eval (clApply cl spine) ctrl)
    evalPointerAM (Pointer p) spine ctrl = readPointer p >>= \ case
      BlackHole -> __IMPOSSIBLE__
      Thunk cl@(Closure Unevaled _ _ _) | callByNeed -> do
        blackHole p
        runAM (Eval cl $ updateThunkCtrl p $ [ApplyK spine | not (null spine)] ++ ctrl)
      Thunk cl -> runAM (Eval (clApply cl spine) ctrl)

    -- 'evalIApplyAM spine ctrl fallback' checks if any 'IApply x y r' has a canonical 'r' (i.e. 0 or 1),
    -- in that case continues evaluating 'x' or 'y' with the rest of 'spine' and same 'ctrl'.
    -- If no such 'IApply' is found we continue with 'fallback'.
    evalIApplyAM :: Spine s -> ControlStack s -> ST s (Blocked Term) -> ST s (Blocked Term)
    evalIApplyAM es ctrl fallback = go es
      where
        -- written as a worker/wrapper to possibly trigger some
        -- specialization wrt fallback
        go []                  = fallback
        go (IApply x y r : es) = do
          br <- evalPointerAM r [] []
          case iview $ ignoreBlocking br of
            IZero -> evalPointerAM x es ctrl
            IOne  -> evalPointerAM y es ctrl
            _     -> (<* blockedOrMeta br) <$> go es
        go (e : es) = go es

    -- Normalise the spine and apply the closure to the result. The closure must be a value closure.
    normaliseArgsAM :: Closure s -> Spine s -> ControlStack s -> ST s (Blocked Term)
    normaliseArgsAM cl []    ctrl = runAM (Eval cl ctrl)  -- nothing to do
    normaliseArgsAM cl spine ctrl =
      case firstHole spine of -- v Only projections, nothing to do. Note clApply_ and not clApply (or we'd loop)
        Nothing       -> runAM (Eval (clApply_ cl spine) ctrl)
        Just (p, cxt) -> evalPointerAM p [] (NormaliseK : ArgK cl cxt : ctrl)

    -- Fall back to slow reduction. This happens if we encounter a definition that's not supported
    -- by the machine (like a primitive function that does not work on literals), or a term that is
    -- not supported (Level and Sort at the moment). In this case we decode the current
    -- focus to a 'Term', call slow reduction and pack up the result in a value closure. If the top
    -- of the control stack is a 'NormaliseK' and the focus is a value closure (i.e. already in
    -- weak-head normal form) we call 'slowNormaliseArgs' and pop the 'NormaliseK' frame. Otherwise
    -- we use 'slowReduceTerm' to compute a weak-head normal form.
    fallbackAM :: AM s -> ST s (Blocked Term)
    fallbackAM (Eval c ctrl) = do
        v <- decodeClosure_ c
        runAM (mkValue $ runReduce $ slow v)
      where mkValue b = evalValue (() <$ b) (ignoreBlocking b) emptyEnv [] ctrl'
            (slow, ctrl') = case ctrl of
              NormaliseK : ctrl'
                | Value{} <- isValue c -> (notBlocked <.> slowNormaliseArgs, ctrl')
              _                        -> (slowReduceTerm, ctrl)
    fallbackAM _ = __IMPOSSIBLE__

    -- If rewriting is enabled, try to apply rewrite rules to the current focus before considering
    -- it a value. The current state must be 'Eval' and the focus a value closure. Take care to only
    -- test the 'hasRewriting' flag once.
    rewriteAM :: AM s -> ST s (Blocked Term)
    rewriteAM = if hasRewriting then rewriteAM' else runAM

    -- Applying rewrite rules to the current focus. This needs to decode the current focus, call
    -- rewriting and pack the result back up in a closure. In case some rewrite rules actually fired
    -- the next state is an unevaluated closure, otherwise it's a value closure.
    rewriteAM' :: AM s -> ST s (Blocked Term)
    rewriteAM' s@(Eval (Closure (Value blk) t env spine) ctrl)
      | null rewr = runAM s
      | otherwise = traceDoc ("R" <+> pretty s) $ do
        v0 <- decodeClosure_ (Closure Unevaled t env [])
        es <- decodeSpine spine
        case runReduce (rewrite blk v0 rewr es) of
          NoReduction b    -> runAM (evalValue (() <$ b) (ignoreBlocking b) emptyEnv [] ctrl)
          YesReduction _ v -> runAM (evalClosure v emptyEnv [] ctrl)
      where rewr = case t of
                     Def f []   -> rewriteRules f
                     Con c _ [] -> rewriteRules (conName c)
                     _          -> __IMPOSSIBLE__
    rewriteAM' _ =
      __IMPOSSIBLE__

    -- Add a NatSucK frame to the control stack. Pack consecutive suc's into a single frame.
    sucCtrl :: ControlStack s -> ControlStack s
    sucCtrl (NatSucK !n : ctrl) = NatSucK (n + 1) : ctrl
    sucCtrl               ctrl  = NatSucK 1 : ctrl

    -- Add a UpdateThunk frame to the control stack. Pack consecutive updates into a single frame.
    updateThunkCtrl :: STPointer s -> ControlStack s -> ControlStack s
    updateThunkCtrl p (UpdateThunk ps : ctrl) = UpdateThunk (p : ps) : ctrl
    updateThunkCtrl p                   ctrl  = UpdateThunk [p] : ctrl

    -- Only unfold delayed (corecursive) definitions if the result is being cased on.
    unfoldDelayed :: ControlStack s -> Bool
    unfoldDelayed []                     = False
    unfoldDelayed (CaseK{}       : _)    = True
    unfoldDelayed (PrimOpK{}     : _)    = False
    unfoldDelayed (NatSucK{}     : _)    = False
    unfoldDelayed (NormaliseK{}  : _)    = False
    unfoldDelayed (ArgK{}        : _)    = False
    unfoldDelayed (UpdateThunk{} : ctrl) = unfoldDelayed ctrl
    unfoldDelayed (ApplyK{}      : ctrl) = unfoldDelayed ctrl
    unfoldDelayed (ForceK{}      : ctrl) = unfoldDelayed ctrl
    unfoldDelayed (EraseK{}      : ctrl) = unfoldDelayed ctrl

    -- When matching is stuck we return the closure from the 'MatchStack' with the appropriate
    -- 'IsValue' set.
    stuckMatch :: Blocked_ -> MatchStack s -> ControlStack s -> ST s (Blocked Term)
    stuckMatch blk (_ :> cl) ctrl = rewriteAM (Eval (mkValue blk cl) ctrl)

    -- On a mismatch we find the next 'CatchAll' on the control stack and
    -- continue matching from there. If there isn't one we get an incomplete
    -- matching error (or get stuck if the function is marked partial).
    failedMatch :: QName -> MatchStack s -> ControlStack s -> ST s (Blocked Term)
    failedMatch f (CatchAll cc spine : stack :> cl) ctrl = runAM (Match f cc spine (stack :> cl) ctrl)
    failedMatch f ([] :> cl) ctrl
        -- Bad work-around for #3870: don't fail hard during instance search.
      | speculative          = rewriteAM (Eval (mkValue (NotBlocked MissingClauses ()) cl) ctrl)
      | f `elem` partialDefs = rewriteAM (Eval (mkValue (NotBlocked MissingClauses ()) cl) ctrl)
      | otherwise            = runReduce $
          traceSLn "impossible" 10 ("Incomplete pattern matching when applying " ++ show f)
                   __IMPOSSIBLE__

    -- Some helper functions to build machine states and closures.
    evalClosure t env spine = Eval (Closure Unevaled t env spine)
    evalValue b t env spine = Eval (Closure (Value b) t env spine)
    evalTrueValue           = evalValue $ notBlocked ()
    trueValue t env spine   = Closure (Value $ notBlocked ()) t env spine
    mkValue b               = setIsValue (Value b)

    -- Building lambdas
    lams :: [Arg String] -> Term -> Term
    lams xs t = foldr lam t xs

    lam :: Arg String -> Term -> Term
    lam x t = Lam (argInfo x) (Abs (unArg x) t)

-- Pretty printing --------------------------------------------------------

instance Pretty a => Pretty (FastCase a) where
  prettyPrec p (FBranches _cop cs suc ls m _) =
    mparens (p > 0) $ vcat (prettyMap cs ++ prettyMap ls ++ prSuc suc ++ prC m)
    where
      prC Nothing = []
      prC (Just x) = ["_ ->" <?> pretty x]

      prSuc Nothing  = []
      prSuc (Just x) = ["suc ->" <?> pretty x]

instance Pretty FastCompiledClauses where
  pretty (FDone xs t) = ("done" <+> prettyList xs) <?> prettyPrec 10 t
  pretty FFail        = "fail"
  pretty (FEta n _ cc ca) =
    text ("eta " ++ show n ++ " of") <?>
      vcat ([ "{} ->" <?> pretty cc ] ++
            [ "_ ->" <?> pretty cc | Just cc <- [ca] ])
  pretty (FCase n bs) | fprojPatterns bs =
    sep [ text $ "project " ++ show n
        , nest 2 $ pretty bs
        ]
  pretty (FCase n bs) =
    text ("case " ++ show n ++ " of") <?> pretty bs

instance Pretty a => Pretty (Thunk a) where
  prettyPrec _ BlackHole  = "<BLACKHOLE>"
  prettyPrec p (Thunk cl) = prettyPrec p cl

instance Pretty (Pointer s) where
  prettyPrec p = prettyPrec p . unsafeDerefPointer

instance Pretty (Closure s) where
  prettyPrec _ (Closure Value{} (Lit (LitString _ unused)) _ _)
    | unused == unusedPointerString = "_"
  prettyPrec p (Closure isV t env spine) =
    mparens (p > 9) $ fsep [ text tag
                           , nest 2 $ prettyPrec 10 t
                           , nest 2 $ prettyList $ zipWith envEntry [0..] (envToList env)
                           , nest 2 $ prettyList spine ]
      where envEntry i c = text ("@" ++ show i ++ " =") <+> pretty c
            tag = case isV of Value{} -> "V"; Unevaled -> "E"

instance Pretty (AM s) where
  prettyPrec p (Eval cl ctrl)  = prettyPrec p cl <?> prettyList ctrl
  prettyPrec p (Match f cc sp stack ctrl) =
    mparens (p > 9) $ sep [ "M" <+> pretty f
                          , nest 2 $ prettyList sp
                          , nest 2 $ prettyPrec 10 cc
                          , nest 2 $ pretty stack
                          , nest 2 $ prettyList ctrl ]

instance Pretty (CatchAllFrame s) where
  pretty CatchAll{} = "CatchAll"

instance Pretty (MatchStack s) where
  pretty ([] :> _) = empty
  pretty (ca :> _) = prettyList ca

instance Pretty (ControlFrame s) where
  prettyPrec p (CaseK f _ _ _ _ mc)       = mparens (p > 9) $ ("CaseK" <+> pretty (qnameName f)) <?> pretty mc
  prettyPrec p (ForceK _ spine0 spine1)   = mparens (p > 9) $ "ForceK" <?> prettyList (spine0 <> spine1)
  prettyPrec p (EraseK _ sp0 sp1 sp2 sp3) = mparens (p > 9) $ sep [ "EraseK"
                                                                  , nest 2 $ prettyList sp0
                                                                  , nest 2 $ prettyList sp1
                                                                  , nest 2 $ prettyList sp2
                                                                  , nest 2 $ prettyList sp3 ]
  prettyPrec _ (NatSucK n)              = text ("+" ++ show n)
  prettyPrec p (PrimOpK f _ vs cls _)   = mparens (p > 9) $ sep [ "PrimOpK" <+> pretty f
                                                                , nest 2 $ prettyList vs
                                                                , nest 2 $ prettyList cls ]
  prettyPrec p (UpdateThunk ps)         = mparens (p > 9) $ "UpdateThunk" <+> text (show (length ps))
  prettyPrec p (ApplyK spine)           = mparens (p > 9) $ "ApplyK" <?> prettyList spine
  prettyPrec p NormaliseK               = "NormaliseK"
  prettyPrec p (ArgK cl _)              = mparens (p > 9) $ sep [ "ArgK" <+> prettyPrec 10 cl ]
