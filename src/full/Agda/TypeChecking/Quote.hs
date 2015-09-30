{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}

module Agda.TypeChecking.Quote where

import Control.Applicative
import Control.Monad.State (runState, get, put)
import Control.Monad.Writer (execWriterT, tell)
import Control.Monad.Trans (lift)

import Data.Char
import Data.Maybe (fromMaybe)
import Data.Traversable (traverse)

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Translation.InternalToAbstract

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Datatypes ( getConHead )
import Agda.TypeChecking.DropArgs
import Agda.TypeChecking.Free
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Exception
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Except
import Agda.Utils.Impossible
import Agda.Utils.Monad ( ifM )
import Agda.Utils.Permutation ( Permutation(Perm), compactP )
import Agda.Utils.String ( Str(Str), unStr )
import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as Set

#include "undefined.h"

data QuotingKit = QuotingKit
  { quoteTermWithKit   :: Term       -> ReduceM Term
  , quoteTypeWithKit   :: Type       -> ReduceM Term
  , quoteClauseWithKit :: Clause     -> ReduceM Term
  , quoteDomWithKit    :: Dom Type -> ReduceM Term
  }

quotingKit :: TCM QuotingKit
quotingKit = do
  hidden          <- primHidden
  instanceH       <- primInstance
  visible         <- primVisible
  relevant        <- primRelevant
  irrelevant      <- primIrrelevant
  nil             <- primNil
  cons            <- primCons
  abs             <- primAbsAbs
  arg             <- primArgArg
  arginfo         <- primArgArgInfo
  var             <- primAgdaTermVar
  lam             <- primAgdaTermLam
  extlam          <- primAgdaTermExtLam
  def             <- primAgdaTermDef
  con             <- primAgdaTermCon
  pi              <- primAgdaTermPi
  sort            <- primAgdaTermSort
  lit             <- primAgdaTermLit
  litNat          <- primAgdaLitNat
  litFloat        <- primAgdaLitFloat
  litChar         <- primAgdaLitChar
  litString       <- primAgdaLitString
  litQName        <- primAgdaLitQName
  normalClause    <- primAgdaClauseClause
  absurdClause    <- primAgdaClauseAbsurd
  varP            <- primAgdaPatVar
  conP            <- primAgdaPatCon
  dotP            <- primAgdaPatDot
  litP            <- primAgdaPatLit
  projP           <- primAgdaPatProj
  absurdP         <- primAgdaPatAbsurd
  set             <- primAgdaSortSet
  setLit          <- primAgdaSortLit
  unsupportedSort <- primAgdaSortUnsupported
  sucLevel        <- primLevelSuc
  lub             <- primLevelMax
  lkit            <- requireLevels
  el              <- primAgdaTypeEl
  Con z _         <- ignoreSharing <$> primZero
  Con s _         <- ignoreSharing <$> primSuc
  unsupported     <- primAgdaTermUnsupported

  let (@@) :: Apply a => ReduceM a -> ReduceM Term -> ReduceM a
      t @@ u = apply <$> t <*> ((:[]) . defaultArg <$> u)

      (!@) :: Apply a => a -> ReduceM Term -> ReduceM a
      t !@ u = pure t @@ u

      (!@!) :: Apply a => a -> Term -> ReduceM a
      t !@! u = pure t @@ pure u

      quoteHiding :: Hiding -> ReduceM Term
      quoteHiding Hidden    = pure hidden
      quoteHiding Instance  = pure instanceH
      quoteHiding NotHidden = pure visible

      quoteRelevance :: Relevance -> ReduceM Term
      quoteRelevance Relevant   = pure relevant
      quoteRelevance Irrelevant = pure irrelevant
      quoteRelevance NonStrict  = pure relevant
      quoteRelevance Forced{}   = pure relevant
      quoteRelevance UnusedArg  = pure relevant

      quoteArgInfo :: ArgInfo -> ReduceM Term
      quoteArgInfo (ArgInfo h r) = arginfo !@ quoteHiding h
                                           @@ quoteRelevance r

      quoteLit :: Literal -> ReduceM Term
      quoteLit l@LitInt{}    = lit !@ (litNat    !@! Lit l)
      quoteLit l@LitFloat{}  = lit !@ (litFloat  !@! Lit l)
      quoteLit l@LitChar{}   = lit !@ (litChar   !@! Lit l)
      quoteLit l@LitString{} = lit !@ (litString !@! Lit l)
      quoteLit l@LitQName{}  = lit !@ (litQName  !@! Lit l)

      -- We keep no ranges in the quoted term, so the equality on terms
      -- is only on the structure.
      quoteSortLevelTerm :: Level -> ReduceM Term
      quoteSortLevelTerm (Max [])              = setLit !@! Lit (LitInt noRange 0)
      quoteSortLevelTerm (Max [ClosedLevel n]) = setLit !@! Lit (LitInt noRange n)
      quoteSortLevelTerm l                     = set !@ quoteTerm (unlevelWithKit lkit l)

      quoteSort :: Sort -> ReduceM Term
      quoteSort (Type t) = quoteSortLevelTerm t
      quoteSort Prop     = pure unsupportedSort
      quoteSort Inf      = pure unsupportedSort
      quoteSort SizeUniv = pure unsupportedSort
      quoteSort DLub{}   = pure unsupportedSort

      quoteType :: Type -> ReduceM Term
      quoteType (El s t) = el !@ quoteSort s @@ quoteTerm t

      quoteQName :: QName -> ReduceM Term
      quoteQName x = pure $ Lit $ LitQName noRange x

      quotePats :: [NamedArg Pattern] -> ReduceM Term
      quotePats ps = list $ map (quoteArg quotePat . fmap namedThing) ps

      quotePat :: Pattern -> ReduceM Term
      quotePat (VarP "()")   = pure absurdP
      quotePat (VarP x)      = varP !@! quoteString x
      quotePat (DotP _)      = pure dotP
      quotePat (ConP c _ ps) = conP !@ quoteQName (conName c) @@ quotePats ps
      quotePat (LitP l)      = litP !@! Lit l
      quotePat (ProjP x)     = projP !@ quoteQName x

      quoteBody :: I.ClauseBody -> Maybe (ReduceM Term)
      quoteBody (Body a) = Just (quoteTerm a)
      quoteBody (Bind b) = quoteBody (absBody b)
      quoteBody NoBody   = Nothing

      quoteClause :: Clause -> ReduceM Term
      quoteClause Clause{namedClausePats = ps, clauseBody = body} =
        case quoteBody body of
          Nothing -> absurdClause !@ quotePats ps
          Just b  -> normalClause !@ quotePats ps @@ b

      list :: [ReduceM Term] -> ReduceM Term
      list []       = pure nil
      list (a : as) = cons !@ a @@ list as

      quoteDom :: (Type -> ReduceM Term) -> Dom Type -> ReduceM Term
      quoteDom q (Dom info t) = arg !@ quoteArgInfo info @@ q t

      quoteAbs :: Subst t a => (a -> ReduceM Term) -> Abs a -> ReduceM Term
      quoteAbs q (Abs s t)   = abs !@! quoteString s @@ q t
      quoteAbs q (NoAbs s t) = abs !@! quoteString s @@ q (raise 1 t)

      quoteArg :: (a -> ReduceM Term) -> Arg a -> ReduceM Term
      quoteArg q (Arg info t) = arg !@ quoteArgInfo info @@ q t

      quoteArgs :: Args -> ReduceM Term
      quoteArgs ts = list (map (quoteArg quoteTerm) ts)

      quoteTerm :: Term -> ReduceM Term
      quoteTerm v =
        case unSpine v of
          Var n es   ->
             let ts = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
             in  var !@! Lit (LitInt noRange $ fromIntegral n) @@ quoteArgs ts
          Lam info t -> lam !@ quoteHiding (getHiding info) @@ quoteAbs quoteTerm t
          Def x es   -> do
            d <- theDef <$> getConstInfo x
            qx d @@ quoteArgs ts
            where
              ts = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
              qx Function{ funExtLam = Just (ExtLamInfo h nh), funClauses = cs } =
                    extlam !@ list (map (quoteClause . dropArgs (h + nh)) cs)
              qx Function{ funCompiled = Just Fail, funClauses = [cl] } =
                    extlam !@ list [quoteClause $ dropArgs (length (clausePats cl) - 1) cl]
              qx _ = def !@! quoteName x
          Con x ts   -> do
            Constructor{conPars = np} <- theDef <$> getConstInfo (conName x)
            let par  = arg !@ (arginfo !@ pure hidden @@ pure relevant) @@ pure unsupported
                pars = replicate np $ par
                args = list $ pars ++ map (quoteArg quoteTerm) ts
            con !@! quoteConName x @@ args
          Pi t u     -> pi !@  quoteDom quoteType t
                            @@ quoteAbs quoteType u
          Level l    -> quoteTerm (unlevelWithKit lkit l)
          Lit lit    -> quoteLit lit
          Sort s     -> sort !@ quoteSort s
          Shared p   -> quoteTerm $ derefPtr p
          MetaV{}    -> pure unsupported
          DontCare{} -> pure unsupported -- could be exposed at some point but we have to take care
  return $ QuotingKit quoteTerm quoteType quoteClause (quoteDom quoteType)

quoteString :: String -> Term
quoteString = Lit . LitString noRange

quoteName :: QName -> Term
quoteName x = Lit (LitQName noRange x)

quoteConName :: ConHead -> Term
quoteConName = quoteName . conName

quoteTerm :: Term -> TCM Term
quoteTerm v = do
  kit <- quotingKit
  runReduceM (quoteTermWithKit kit v)

quoteType :: Type -> TCM Term
quoteType v = do
  kit <- quotingKit
  runReduceM (quoteTypeWithKit kit v)

quoteDom :: Dom Type -> TCM Term
quoteDom v = do
  kit <- quotingKit
  runReduceM (quoteDomWithKit kit v)
