-- | Checking definitions of typed/untyped pattern synonyms

module Agda.TypeChecking.Rules.PatternSynDef where

import Data.Maybe
import Data.Void

import Agda.Syntax.Common
import Agda.Syntax.Info

import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Abstract.Views as A
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Implicit

import Agda.TypeChecking.Rules.LHS ( disambiguateConstructor )
import Agda.TypeChecking.Rules.Term

import Agda.Utils.Monad
import Agda.Utils.Impossible


checkPatternSynDef :: QName -> Maybe (A.DefInfo, A.Expr) -> [Arg A.BindName] ->
                      A.Pattern' Void -> TCM ()
checkPatternSynDef name Nothing as rhs = undefined
checkPatternSynDef name (Just (i, e)) as rhs = do
  ty <- isType_ e
  checkTyped name i ty as rhs

checkTyped :: QName -> A.DefInfo -> Type -> [Arg A.BindName] ->
              A.Pattern' Void -> TCM ()
checkTyped name i sig as rhs =
  -- 1. Check left hand side
  checkLHS sig as $ \ target -> do
  -- 2. Sanity check: pattern syn targets data or record type
    target <- reduce target
    case unEl target of
      Def tyCon _ -> do
        Just{} <- isDataOrRecordType tyCon
        pure ()
      _ -> genericError "Expected a data or record type as the target of the pattern synonym"
  -- 3. Check right hand side
    checkRHS target rhs $ \ rhs ->
  -- 4. Register "constructor"
      undefined

checkLHS :: Type -> [Arg A.BindName] -> ({- Telescope -> -} Type -> TCM a) -> TCM a
checkLHS ty []           k = k ty
checkLHS ty xxs@(x : xs) k = do
  ty <- reduce ty
  case unEl ty of
    Pi a b | not (sameHiding x a) ->
      if visible a
      then genericError "Tried to bind an implicit argument but expected an explicit one"
      else addContext (absName b, a) $ underAbstractionAbs a b $ \b -> checkLHS b xxs k
    -- In the rest, `a` and `x` do have the same visibility
    Pi a b | otherwise ->
      lambdaAddContext (A.unBind (unArg x)) (absName b) a $
        underAbstractionAbs a b $ \b -> checkLHS b xs k
    -- TODO: Allow named arguments & use the names to align the sequences of implicits
    -- e.g.
    -- c : {a b c d} {x} -> ...
    -- c {x = x} = ...
    _ -> genericError "Tried to bind an argument but target type is not a Pi"


checkRHS :: Type                 -- ^ Has already been reduced
         -> A.Pattern' Void
         -> (DeBruijnPattern -> TCM a)
         -> TCM a
checkRHS ty p k = case p of
  A.VarP bx -> do
    let x = A.unBind bx
    (Var i [], candidate) <- getVarInfo x
    equalType ty (unDom candidate)
    k (VarP (PatternInfo (PatOVar x) []) (DBPatVar "x" i))

  A.WildP _ -> do
    -- Wildcard pattern is valid at any type. This will be turned back into
    -- a WildP when unfolding the pattern synonym.
    k (VarP (PatternInfo PatOWild []) (DBPatVar "_" (-1)))

  A.LitP l -> do

    _ <- checkLiteral l ty

    -- This check may desugar a literal using available instances
    -- (using the mechanism in `Agda.Builtin.FromNat` for example)
    -- We do not use the desugared result: inlining pattern synonyms
    -- in the Agda source should not suddenly break valid code

    -- pattern
    --   two : Fin 3        -- checkLiteral would allow us to elaborate this to
    --   two = 2            -- two = suc (suc zero)

    -- f : Fin 3 -> Fin 3   -- which would make this typecheck
    -- f two = zero
    -- f _ = zero

    -- f : Fin 3 -> Fin 3   -- but not this because we currently do not have support
    -- f 2 = zero           -- for overloaded literals on the LHS!
    -- f _ = zero

    k (LitP (PatternInfo PatOLit []) l)

  A.ConP _ con ps -> do
    (qn, isRec, args) <- case unEl ty of
      Def f es -> do
        Just dr <- isDataOrRecordType f
        let b = case dr of { IsData -> False ; _ -> True }
        pure (f, b, fromMaybe __IMPOSSIBLE__ $ allApplyElims es)
      _ -> genericError "Expected a data or record type"
    (con, ty) <- disambiguateConstructor con qn args
    checkArguments ty ps $ \ naps -> do
      let pi = noConPatternInfo { conPInfo   = PatternInfo PatOCon []
                                , conPRecord = isRec
                                }
      k (ConP con pi naps)

{-
  | RecP PatInfo [FieldAssignment' (Pattern' e)]
-}

checkArguments :: Type -> A.NAPs Void -> (NAPs -> TCM a) -> TCM a
checkArguments ty []           k = k []
checkArguments ty pps@(p : ps) k = do
  let np = bareNameOf (unArg p)
      expand NotHidden _  = False
      expand h         nm = not (sameHiding h p) || maybe False (nm /=) np
  (nargs, ty) <- implicitNamedArgs (-1) expand ty
  case unEl ty of
    Pi a b | not (sameHiding a p) -> genericError "Expected implicit type, got explicit one"
    Pi a b | otherwise -> do
      checkRHS (unDom a) (namedThing $ unArg p) $ \ p' ->
        undefined

-- Ideally:
--        checkArguments (b [p'/0]) ps $ \ ps' ->
--          k (map undefined nargs ++ p' : ps')

-- Because:
-- f : Sig N (Vec N) -> ??
-- f (suc zero, p : Vec N 1) = ?

-- But:
-- p' is a pattern, not a term

