{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE PatternGuards #-}

module Agda.TypeChecking.Quote where

import Control.Applicative
import Control.Monad.State (evalState, get, put)
import Control.Monad.Writer (execWriterT, tell)
import Control.Monad.Error (catchError)

import Data.Maybe (fromMaybe)
import Data.Traversable (traverse)
import Data.Char

import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Internal as I
import Agda.Syntax.Common
import Agda.Syntax.Translation.InternalToAbstract

import {-# SOURCE #-} Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.DropArgs
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Free

import Agda.Utils.String
import Agda.Utils.Permutation

import Agda.Utils.Monad

#include "../undefined.h"
import Agda.Utils.Impossible

quotingKit :: TCM (Term -> ReduceM Term, Type -> ReduceM Term, Clause -> ReduceM Term)
quotingKit = do
  hidden          <- primHidden
  instanceH       <- primInstance
  visible         <- primVisible
  relevant        <- primRelevant
  irrelevant      <- primIrrelevant
  nil             <- primNil
  cons            <- primCons
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
  el              <- primAgdaTypeEl
  Con z _         <- ignoreSharing <$> primZero
  Con s _         <- ignoreSharing <$> primSuc
  unsupported     <- primAgdaTermUnsupported

  let (@@) :: Apply a => ReduceM a -> ReduceM Term -> ReduceM a
      t @@ u = apply <$> t <*> ((:[]) . defaultArg <$> u)

      (!@) :: Apply a => a -> ReduceM Term -> ReduceM a
      t !@  u = pure t @@ u

      (!@!) :: Apply a => a -> Term -> ReduceM a
      t !@! u = pure t @@ pure u

      quoteHiding Hidden    = pure hidden
      quoteHiding Instance  = pure instanceH
      quoteHiding NotHidden = pure visible
      quoteRelevance Relevant   = pure relevant
      quoteRelevance Irrelevant = pure irrelevant
      quoteRelevance NonStrict  = pure relevant
      quoteRelevance Forced     = pure relevant
      quoteRelevance UnusedArg  = pure relevant
      quoteColors _ = nil -- TODO guilhem
      quoteArgInfo (ArgInfo h r cs) = arginfo !@ quoteHiding h
                                              @@ quoteRelevance r
                                --              @@ quoteColors cs
      quoteLit l@LitInt{}    = lit !@ (litNat    !@! Lit l)
      quoteLit l@LitFloat{}  = lit !@ (litFloat  !@! Lit l)
      quoteLit l@LitChar{}   = lit !@ (litChar   !@! Lit l)
      quoteLit l@LitString{} = lit !@ (litString !@! Lit l)
      quoteLit l@LitQName{}  = lit !@ (litQName  !@! Lit l)
      -- We keep no ranges in the quoted term, so the equality on terms
      -- is only on the structure.
      quoteSortLevelTerm (Max [])              = setLit !@! Lit (LitInt noRange 0)
      quoteSortLevelTerm (Max [ClosedLevel n]) = setLit !@! Lit (LitInt noRange n)
      quoteSortLevelTerm (Max [Plus 0 (NeutralLevel v)]) = set !@ quote v
      quoteSortLevelTerm _                     = pure unsupportedSort
      quoteSort (Type t)    = quoteSortLevelTerm t
      quoteSort Prop        = pure unsupportedSort
      quoteSort Inf         = pure unsupportedSort
      quoteSort DLub{}      = pure unsupportedSort
      quoteType (El s t) = el !@ quoteSort s @@ quote t

      quoteQName x = pure $ Lit $ LitQName noRange x
      quotePats ps = list $ map (quoteArg quotePat . fmap namedThing) ps
      quotePat (VarP "()")   = pure absurdP
      quotePat (VarP _)      = pure varP
      quotePat (DotP _)      = pure dotP
      quotePat (ConP c _ ps) = conP !@ quoteQName (conName c) @@ quotePats ps
      quotePat (LitP l)      = litP !@! Lit l
      quotePat (ProjP x)     = projP !@ quoteQName x
      quoteBody (Body a) = Just (quote a)
      quoteBody (Bind b) = quoteBody (absBody b)
      quoteBody NoBody   = Nothing
      quoteClause Clause{namedClausePats = ps, clauseBody = body} =
        case quoteBody body of
          Nothing -> absurdClause !@ quotePats ps
          Just b  -> normalClause !@ quotePats ps @@ b

      list [] = pure nil
      list (a : as) = cons !@ a @@ list as
      quoteDom q (Dom info t) = arg !@ quoteArgInfo info @@ q t
      quoteArg q (Arg info t) = arg !@ quoteArgInfo info @@ q t
      quoteArgs ts = list (map (quoteArg quote) ts)
      quote v =
        case unSpine v of
          Var n es   ->
             let ts = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
             in  var !@! Lit (LitInt noRange $ fromIntegral n) @@ quoteArgs ts
          Lam info t -> lam !@ quoteHiding (getHiding info) @@ quote (absBody t)
          Def x es   -> do
            d <- theDef <$> getConstInfo x
            qx d @@ quoteArgs ts
            where
              ts = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
              qx Function{ funExtLam = Just (h, nh), funClauses = cs } =
                    extlam !@ list (map (quoteClause . dropArgs (h + nh)) cs)
              qx Function{ funCompiled = Just Fail, funClauses = [cl] } =
                    extlam !@ list [quoteClause $ dropArgs (length (clausePats cl) - 1) cl]
              qx _ = def !@! quoteName x
          Con x ts   -> con !@! quoteConName x @@ quoteArgs ts
          Pi t u     -> pi !@ quoteDom quoteType t
                             @@ quoteType (absBody u)
          Level _    -> pure unsupported
          Lit lit    -> quoteLit lit
          Sort s     -> sort !@ quoteSort s
          Shared p   -> quote $ derefPtr p
          MetaV{}    -> pure unsupported
          DontCare{} -> pure unsupported -- could be exposed at some point but we have to take care
          ExtLam{}   -> __IMPOSSIBLE__
  return (quote, quoteType, quoteClause)

quoteName :: QName -> Term
quoteName x = Lit (LitQName noRange x)

quoteConName :: ConHead -> Term
quoteConName = quoteName . conName

quoteTerm :: Term -> TCM Term
quoteTerm v = do
  (f, _, _) <- quotingKit
  runReduceM (f v)

quoteType :: Type -> TCM Term
quoteType v = do
  (_, f, _) <- quotingKit
  runReduceM (f v)

agdaTermType :: TCM Type
agdaTermType = El (mkType 0) <$> primAgdaTerm

qNameType :: TCM Type
qNameType = El (mkType 0) <$> primQName

isCon :: ConHead -> TCM Term -> TCM Bool
isCon con tm = do t <- tm
                  case ignoreSharing t of
                    Con con' _ -> return (con == con')
                    _ -> return False

unquoteFailedGeneric :: String -> TCM a
unquoteFailedGeneric msg = typeError . GenericError $ "Unable to unquote the " ++ msg

unquoteFailed :: String -> String -> Term -> TCM a
unquoteFailed kind msg t = do doc <- prettyTCM t
                              unquoteFailedGeneric $ "term (" ++ show doc ++ ") of type " ++ kind ++ ".\nReason: " ++ msg ++ "."

class Unquote a where
  unquote :: Term -> TCM a

unquoteH :: Unquote a => I.Arg Term -> TCM a
unquoteH a | isHidden a && isRelevant a =
    unquote $ unArg a
unquoteH _ = unquoteFailedGeneric "argument. It should be `hidden'."

unquoteN :: Unquote a => I.Arg Term -> TCM a
unquoteN a | notHidden a && isRelevant a =
    unquote $ unArg a
unquoteN _ = unquoteFailedGeneric "argument. It should be `visible'"

choice :: Monad m => [(m Bool, m a)] -> m a -> m a
choice [] dflt = dflt
choice ((mb, mx) : mxs) dflt = ifM mb mx $ choice mxs dflt

ensureDef :: QName -> TCM QName
ensureDef x = do
  i <- (theDef <$> getConstInfo x) `catchError` \_ -> return Axiom  -- for recursive unquoteDecl
  case i of
    Constructor{} -> do
      def <- prettyTCM =<< primAgdaTermDef
      con <- prettyTCM =<< primAgdaTermCon
      c   <- prettyTCM x
      setCurrentRange (getRange x) $ typeError $ GenericError $ "Use " ++ show con ++ " instead of " ++ show def ++ " for constructor " ++ show c
    _ -> return x

ensureCon :: QName -> TCM QName
ensureCon x = do
  i <- (theDef <$> getConstInfo x) `catchError` \_ -> return Axiom  -- for recursive unquoteDecl
  case i of
    Constructor{} -> return x
    _ -> do
      def <- prettyTCM =<< primAgdaTermDef
      con <- prettyTCM =<< primAgdaTermCon
      f   <- prettyTCM x
      setCurrentRange (getRange x) $ typeError $ GenericError $ "Use " ++ show def ++ " instead of " ++ show con ++ " for non-constructor " ++ show f

pickName :: Type -> String
pickName a =
  case unEl a of
    Pi{}   -> "f"
    Sort{} -> "A"
    Def d _ | c:_ <- show (qnameName d),
              isAlpha c -> [toLower c]
    _    -> "_"

instance Unquote I.ArgInfo where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Con c [h,r] -> do
        choice
          [(c `isCon` primArgArgInfo, ArgInfo <$> unquoteN h <*> unquoteN r <*> return [])]
          (unquoteFailed "ArgInfo" "arity 2 and not the `arginfo' constructor" t)
      _ -> unquoteFailed "ArgInfo" "not of arity 2" t

instance Unquote a => Unquote (I.Arg a) where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Con c [info,x] -> do
        choice
          [(c `isCon` primArgArg, Arg <$> unquoteN info <*> unquoteN x)]
          (unquoteFailed "Arg" "arity 2 and not the `arg' constructor" t)
      _ -> unquoteFailed "Arg" "not of arity 2" t

-- Andreas, 2013-10-20: currently, post-fix projections are not part of the
-- quoted syntax.
instance Unquote a => Unquote (Elim' a) where
  unquote t = Apply <$> unquote t

instance Unquote Integer where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Lit (LitInt _ n) -> return n
      _ -> unquoteFailed "Integer" "not a literal integer" t

instance Unquote Double where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Lit (LitFloat _ x) -> return x
      _ -> unquoteFailed "Float" "not a literal float" t

instance Unquote Char where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Lit (LitChar _ x) -> return x
      _ -> unquoteFailed "Char" "not a literal char" t

instance Unquote Str where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Lit (LitString _ x) -> return (Str x)
      _ -> unquoteFailed "String" "not a literal string" t

instance Unquote a => Unquote [a] where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Con c [x,xs] -> do
        choice
          [(c `isCon` primCons, (:) <$> unquoteN x <*> unquoteN xs)]
          (unquoteFailed "List" "arity 2 and not the `∷' constructor" t)
      Con c [] -> do
        choice
          [(c `isCon` primNil, return [])]
          (unquoteFailed "List" "arity 0 and not the `[]' constructor" t)
      _ -> unquoteFailed "List" "neither `[]' nor `∷'" t

instance Unquote Hiding where
  unquote t = do
    t <- reduce t
    let err = unquoteFailed "Hiding" "neither `hidden' nor `visible'" t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [(c `isCon` primHidden,  return Hidden)
          ,(c `isCon` primInstance, return Instance)
          ,(c `isCon` primVisible, return NotHidden)]
          err
      Con c vs -> unquoteFailed "Hiding" "the value is a constructor, but its arity is not 0" t
      _        -> err

instance Unquote Relevance where
  unquote t = do
    t <- reduce t
    let err = unquoteFailed "Relevance" "neither `relevant' or `irrelevant'" t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [(c `isCon` primRelevant,   return Relevant)
          ,(c `isCon` primIrrelevant, return Irrelevant)]
          err
      Con c vs -> unquoteFailed "Relevance" "the value is a constructor, but its arity is not 0" t
      _        -> err

instance Unquote QName where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Lit (LitQName _ x) -> return x
      _                  -> unquoteFailed "QName" "not a literal qname value" t

instance Unquote ConHead where
  unquote t = getConHead =<< ensureCon =<< unquote t

instance Unquote a => Unquote (Abs a) where
  unquote t = Abs "_" <$> unquote t

instance Unquote Sort where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [(c `isCon` primAgdaSortUnsupported, pure $ Type $ Max [Plus 0 $ UnreducedLevel $ hackReifyToMeta])]
          __IMPOSSIBLE__
      Con c [u] -> do
        choice
          [(c `isCon` primAgdaSortSet, Type <$> unquoteN u)
          ,(c `isCon` primAgdaSortLit, Type . levelMax . (:[]) . ClosedLevel <$> unquoteN u)]
          (unquoteFailed "Sort" "arity 1 and not the `set' or the `lit' constructors" t)
      _ -> unquoteFailed "Sort" "not of arity 0 nor 1" t

instance Unquote Level where
  unquote l = Max . (:[]) . Plus 0 . UnreducedLevel <$> unquote l

instance Unquote Type where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Con c [s, u] -> do
        choice
          [(c `isCon` primAgdaTypeEl, El <$> unquoteN s <*> unquoteN u)]
          (unquoteFailed "Type" "arity 2 and not the `el' constructor" t)
      _ -> unquoteFailed "Type" "not of arity 2" t

instance Unquote Literal where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Con c [x] ->
        choice
          [ (c `isCon` primAgdaLitNat,    LitInt    noRange <$> unquoteN x)
          , (c `isCon` primAgdaLitFloat,  LitFloat  noRange <$> unquoteN x)
          , (c `isCon` primAgdaLitChar,   LitChar   noRange <$> unquoteN x)
          , (c `isCon` primAgdaLitString, LitString noRange . getStr <$> unquoteN x)
          , (c `isCon` primAgdaLitQName,  LitQName  noRange <$> unquoteN x) ]
          (unquoteFailed "Literal" "not a literal constructor" t)
      _ -> unquoteFailed "Literal" "not a literal constructor" t

instance Unquote Term where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Con c [] ->
        choice
          [(c `isCon` primAgdaTermUnsupported, pure hackReifyToMeta)]
          (unquoteFailed "Term" "arity 0 and not the `unsupported' constructor" t)

      Con c [x] -> do
        choice
          [ (c `isCon` primAgdaTermSort,   Sort <$> unquoteN x)
          , (c `isCon` primAgdaTermLit,    Lit <$> unquoteN x) ]
          (unquoteFailed "Term" "bad constructor" t)

      Con c [x, y] ->
        choice
          [ (c `isCon` primAgdaTermVar, Var <$> (fromInteger <$> unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermCon, Con <$> unquoteN x <*> unquoteN y)
          , (c `isCon` primAgdaTermDef, Def <$> (ensureDef =<< unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermLam, Lam <$> (flip setHiding defaultArgInfo <$> unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermPi,  mkPi <$> (domFromArg <$> unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermExtLam, mkExtLam <$> unquoteN x <*> unquoteN y) ]
          (unquoteFailed "Term" "bad term constructor" t)
        where
          mkExtLam = ExtLam
          mkPi a (Abs _ b) = Pi a (Abs x b)
            where x | 0 `freeIn` b = pickName (unDom a)
                    | otherwise    = "_"
          mkPi _ NoAbs{} = __IMPOSSIBLE__

      Con{} -> unquoteFailed "Term" "neither arity 0 nor 1 nor 2" t
      Lit{} -> unquoteFailed "Term" "unexpected literal" t
      _ -> unquoteFailed "Term" "not a constructor" t

instance Unquote Pattern where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [ (c `isCon` primAgdaPatVar,    pure (VarP "x"))
          , (c `isCon` primAgdaPatAbsurd, pure (VarP "()"))
          , (c `isCon` primAgdaPatDot,    pure (DotP hackReifyToMeta))
          ] __IMPOSSIBLE__
      Con c [x] -> do
        choice
          [ (c `isCon` primAgdaPatProj, ProjP <$> unquoteN x)
          , (c `isCon` primAgdaPatLit,  LitP  <$> unquoteN x) ]
          __IMPOSSIBLE__
      Con c [x, y] -> do
        choice
          [ (c `isCon` primAgdaPatCon, flip ConP Nothing <$> unquoteN x <*> (map (fmap unnamed) <$> unquoteN y)) ]
          __IMPOSSIBLE__
      _ -> unquoteFailed "Pattern" "not a constructor" t

data UnquotedFunDef = UnQFun Type [Clause]

instance Unquote Clause where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Con c [x] -> do
        choice
          [ (c `isCon` primAgdaClauseAbsurd, mkClause Nothing <$> unquoteN x) ]
          __IMPOSSIBLE__
      Con c [x, y] -> do
        choice
          [ (c `isCon` primAgdaClauseClause, mkClause . Just <$> unquoteN y <*> unquoteN x) ]
          __IMPOSSIBLE__
      _ -> unquoteFailed "Pattern" "not a constructor" t
    where
      mkClause :: Maybe Term -> [I.Arg Pattern] -> I.Clause
      mkClause b ps0 =
        Clause { clauseRange     = noRange
               , clauseTel       = dummyTel n'
               , clausePerm      = Perm n vs
               , namedClausePats = ps
               , clauseBody      = mkBody n b
               , clauseType      = Nothing }
        where
          ps = map (fmap unnamed) ps0
          n  = vars True ps  -- with dot patterns
          n' = vars False ps -- without dot patterns
          dummyTel 0 = EmptyTel
          dummyTel n = ExtendTel (defaultDom typeDontCare) (Abs "x" $ dummyTel (n - 1))
          mkBody 0 b = maybe NoBody Body b
          mkBody n b = Bind $ Abs "x" $ mkBody (n - 1) b
          vars d ps = sum $ map (vars' d . namedArg) ps
          vars' d (ConP _ _ ps) = vars d ps
          vars' d VarP{}      = 1
          vars' d DotP{}      = if d then 1 else 0
          vars' d LitP{}      = 0
          vars' d ProjP{}     = 0

          vs = evalState (execWriterT $ mapM_ (computePerm . namedArg) ps) 0
          next = do n <- get; put (n + 1); return n

          computePerm (ConP _ _ ps) = mapM_ (computePerm . namedArg) ps
          computePerm VarP{}        = tell . (:[]) =<< next
          computePerm DotP{}        = () <$ next
          computePerm LitP{}        = return ()
          computePerm ProjP{}       = return ()

instance Unquote UnquotedFunDef where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Con c [x, y] -> do
        choice
          [ (c `isCon` primAgdaFunDefCon, UnQFun <$> unquoteN x <*> unquoteN y) ]
          __IMPOSSIBLE__
      _ -> unquoteFailed "Pattern" "not a constructor" t

reifyUnquoted :: Reify a e => a -> TCM e
reifyUnquoted = nowReifyingUnquoted . disableDisplayForms . withShowAllArguments . reify

