{-# OPTIONS_GHC -fwarn-missing-signatures #-}

{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Agda.TypeChecking.Quote where

import Control.Applicative
import Control.Monad.State (evalState, get, put)
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

import Agda.Utils.Except
import Agda.Utils.Impossible
import Agda.Utils.Monad ( ifM )
import Agda.Utils.Permutation ( Permutation(Perm) )
import Agda.Utils.String ( Str(Str), unStr )
import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as Set

#include "undefined.h"

data QuotingKit = QuotingKit
  { quoteTermWithKit   :: Term       -> ReduceM Term
  , quoteTypeWithKit   :: Type       -> ReduceM Term
  , quoteClauseWithKit :: Clause     -> ReduceM Term
  , quoteDomWithKit    :: I.Dom Type -> ReduceM Term
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
      quoteRelevance Forced     = pure relevant
      quoteRelevance UnusedArg  = pure relevant

--      quoteColors _ = nil -- TODO guilhem

      quoteArgInfo :: I.ArgInfo -> ReduceM Term
      quoteArgInfo (ArgInfo h r cs) = arginfo !@ quoteHiding h
                                              @@ quoteRelevance r
                                --              @@ quoteColors cs

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
      quoteSort DLub{}   = pure unsupportedSort

      quoteType :: Type -> ReduceM Term
      quoteType (El s t) = el !@ quoteSort s @@ quoteTerm t

      quoteQName :: QName -> ReduceM Term
      quoteQName x = pure $ Lit $ LitQName noRange x

      quotePats :: [I.NamedArg Pattern] -> ReduceM Term
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

      quoteDom :: (Type -> ReduceM Term) -> I.Dom Type -> ReduceM Term
      quoteDom q (Dom info t) = arg !@ quoteArgInfo info @@ q t

      quoteAbs :: Subst a => (a -> ReduceM Term) -> Abs a -> ReduceM Term
      quoteAbs q (Abs s t)   = abs !@! quoteString s @@ q t
      quoteAbs q (NoAbs s t) = abs !@! quoteString s @@ q (raise 1 t)

      quoteArg :: (a -> ReduceM Term) -> I.Arg a -> ReduceM Term
      quoteArg q (Arg info t) = arg !@ quoteArgInfo info @@ q t

      quoteArgs :: I.Args -> ReduceM Term
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
              qx Function{ funExtLam = Just (h, nh), funClauses = cs } =
                    extlam !@ list (map (quoteClause . dropArgs (h + nh)) cs)
              qx Function{ funCompiled = Just Fail, funClauses = [cl] } =
                    extlam !@ list [quoteClause $ dropArgs (length (clausePats cl) - 1) cl]
              qx _ = def !@! quoteName x
          Con x ts   -> con !@! quoteConName x @@ quoteArgs ts
          Pi t u     -> pi !@  quoteDom quoteType t
                            @@ quoteAbs quoteType u
          Level l    -> quoteTerm (unlevelWithKit lkit l)
          Lit lit    -> quoteLit lit
          Sort s     -> sort !@ quoteSort s
          Shared p   -> quoteTerm $ derefPtr p
          MetaV{}    -> pure unsupported
          DontCare{} -> pure unsupported -- could be exposed at some point but we have to take care
          ExtLam{}   -> __IMPOSSIBLE__
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

quoteDom :: I.Dom Type -> TCM Term
quoteDom v = do
  kit <- quotingKit
  runReduceM (quoteDomWithKit kit v)

agdaTermType :: TCM Type
agdaTermType = El (mkType 0) <$> primAgdaTerm

agdaTypeType :: TCM Type
agdaTypeType = El (mkType 0) <$> primAgdaType

qNameType :: TCM Type
qNameType = El (mkType 0) <$> primQName

type UnquoteM = ExceptionT UnquoteError TCM

runUnquoteM :: UnquoteM a -> TCM (Either UnquoteError a)
runUnquoteM = runExceptionT

isCon :: ConHead -> TCM Term -> UnquoteM Bool
isCon con tm = do t <- lift tm
                  case ignoreSharing t of
                    Con con' _ -> return (con == con')
                    _ -> return False

{-unquoteFailedGeneric :: String -> UnquoteM a
unquoteFailedGeneric msg = typeError . GenericError $ "Unable to unquote the " ++ msg

unquoteFailed :: String -> String -> Term -> TCM a
unquoteFailed kind msg t = do doc <- prettyTCM t
                              unquoteFailedGeneric $ "term (" ++ show doc ++ ") of type " ++ kind ++ ".\nReason: " ++ msg ++ "."
-}
class Unquote a where
  unquote :: Term -> UnquoteM a

unquoteH :: Unquote a => I.Arg Term -> UnquoteM a
unquoteH a | isHidden a && isRelevant a =
    unquote $ unArg a
unquoteH a = throwException $ BadVisibility "hidden"  a

unquoteN :: Unquote a => I.Arg Term -> UnquoteM a
unquoteN a | notHidden a && isRelevant a =
    unquote $ unArg a
unquoteN a = throwException $ BadVisibility "visible" a

choice :: Monad m => [(m Bool, m a)] -> m a -> m a
choice [] dflt = dflt
choice ((mb, mx) : mxs) dflt = ifM mb mx $ choice mxs dflt

ensureDef :: QName -> UnquoteM QName
ensureDef x = do
  i <- (theDef <$> getConstInfo x) `catchError` \_ -> return Axiom  -- for recursive unquoteDecl
  case i of
    Constructor{} -> do
      def <- lift $ prettyTCM =<< primAgdaTermDef
      con <- lift $ prettyTCM =<< primAgdaTermCon
      throwException $ ConInsteadOfDef x (show def) (show con)
    _ -> return x

ensureCon :: QName -> UnquoteM QName
ensureCon x = do
  i <- (theDef <$> getConstInfo x) `catchError` \_ -> return Axiom  -- for recursive unquoteDecl
  case i of
    Constructor{} -> return x
    _ -> do
      def <- lift $ prettyTCM =<< primAgdaTermDef
      con <- lift $ prettyTCM =<< primAgdaTermCon
      throwException $ DefInsteadOfCon x (show def) (show con)

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
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [h,r] -> do
        choice
          [(c `isCon` primArgArgInfo, ArgInfo <$> unquoteN h <*> unquoteN r <*> return [])]
          (throwException $ BadConstructor "ArgInfo" "arity 2 and not the `arginfo' constructor" t)
      Con c _ -> throwException $ BadConstructor "ArgInfo" "not of arity 2" t
      _ -> throwException $ NotAConstructor "ArgInfo" t

instance Unquote a => Unquote (I.Arg a) where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [info,x] -> do
        choice
          [(c `isCon` primArgArg, Arg <$> unquoteN info <*> unquoteN x)]
          (throwException $ BadConstructor "Arg" "arity 2 and not the `arg' constructor" t)
      Con c _ -> throwException $ BadConstructor "Arg" "not of arity 2" t
      _ -> throwException $ NotAConstructor "Arg" t

-- Andreas, 2013-10-20: currently, post-fix projections are not part of the
-- quoted syntax.
instance Unquote a => Unquote (Elim' a) where
  unquote t = Apply <$> unquote t

instance Unquote Integer where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Lit (LitInt _ n) -> return n
      _ -> throwException $ NotALiteral "Integer" t

instance Unquote Double where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Lit (LitFloat _ x) -> return x
      _ -> throwException $ NotALiteral "Float" t

instance Unquote Char where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Lit (LitChar _ x) -> return x
      _ -> throwException $ NotALiteral "Char" t

instance Unquote Str where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Lit (LitString _ x) -> return (Str x)
      _ -> throwException $ NotALiteral "String" t

unquoteString :: Term -> UnquoteM String
unquoteString x = unStr <$> unquote x

unquoteNString :: I.Arg Term -> UnquoteM String
unquoteNString x = unStr <$> unquoteN x

instance Unquote a => Unquote [a] where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [x,xs] -> do
        choice
          [(c `isCon` primCons, (:) <$> unquoteN x <*> unquoteN xs)]
          (throwException $ BadConstructor "List" "arity 2 and not the `∷' constructor" t)
      Con c [] -> do
        choice
          [(c `isCon` primNil, return [])]
          (throwException $ BadConstructor "List" "arity 0 and not the `[]' constructor" t)
      Con c _ -> throwException $ BadConstructor "List" "neither `[]' nor `∷'" t
      _ -> throwException $ NotAConstructor "List" t

instance Unquote Hiding where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [(c `isCon` primHidden,  return Hidden)
          ,(c `isCon` primInstance, return Instance)
          ,(c `isCon` primVisible, return NotHidden)]
          (throwException $ BadConstructor "Hiding" "neither `hidden' nor `visible'" t)
      Con c vs -> throwException $ BadConstructor "Hiding" "the value is a constructor, but its arity is not 0" t
      _        -> throwException $ NotAConstructor "Hiding" t

instance Unquote Relevance where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [(c `isCon` primRelevant,   return Relevant)
          ,(c `isCon` primIrrelevant, return Irrelevant)]
          (throwException $ BadConstructor "Relevance" "neither `relevant' or `irrelevant'" t)
      Con c vs -> throwException $ BadConstructor "Relevance" "the value is a constructor, but its arity is not 0" t
      _        -> throwException $ NotAConstructor "Relevance" t

instance Unquote QName where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Lit (LitQName _ x) -> return x
      _                  -> throwException $ NotALiteral "QName" t

instance Unquote ConHead where
  unquote t = lift . getConHead =<< ensureCon =<< unquote t

instance Unquote a => Unquote (Abs a) where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [x,y] -> do
        choice
          [(c `isCon` primAbsAbs, Abs <$> (hint <$> unquoteNString x) <*> unquoteN y)]
          (throwException $ BadConstructor "Abs" "arity 2 and not the `abs' constructor (ABSABS builtin)" t)
      Con c _ -> throwException $ BadConstructor "Abs" "not an arity 2 constructor" t
      _ -> throwException $ NotAConstructor "Abs" t

    where hint x | not (null x) = x
                 | otherwise    = "_"

instance Unquote Sort where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [(c `isCon` primAgdaSortUnsupported, pure $ Type $ Max [Plus 0 $ UnreducedLevel $ hackReifyToMeta])]
          __IMPOSSIBLE__
      Con c [u] -> do
        choice
          [(c `isCon` primAgdaSortSet, Type <$> unquoteN u)
          ,(c `isCon` primAgdaSortLit, Type . levelMax . (:[]) . ClosedLevel <$> unquoteN u)]
          (throwException $ BadConstructor "Sort" "arity 1 and not the `set' or the `lit' constructors" t)
      Con c _ -> throwException $ BadConstructor "Sort" "not of arity 0 nor 1" t
      _ -> throwException $ NotAConstructor "Sort" t

instance Unquote Level where
  unquote l = Max . (:[]) . Plus 0 . UnreducedLevel <$> unquote l

instance Unquote Type where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [s, u] -> do
        choice
          [(c `isCon` primAgdaTypeEl, El <$> unquoteN s <*> unquoteN u)]
          (throwException $ BadConstructor "Type" "arity 2 and not the `el' constructor" t)
      Con c _ -> throwException $ BadConstructor "Type" "not of arity 2" t
      _ -> throwException $ NotAConstructor "Type" t

instance Unquote Literal where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [x] ->
        choice
          [ (c `isCon` primAgdaLitNat,    LitInt    noRange <$> unquoteN x)
          , (c `isCon` primAgdaLitFloat,  LitFloat  noRange <$> unquoteN x)
          , (c `isCon` primAgdaLitChar,   LitChar   noRange <$> unquoteN x)
          , (c `isCon` primAgdaLitString, LitString noRange <$> unquoteNString x)
          , (c `isCon` primAgdaLitQName,  LitQName  noRange <$> unquoteN x) ]
          (throwException $ BadConstructor "Literal" "not a literal constructor" t)
      Con c _ -> throwException $ BadConstructor "Literal" "not a literal constructor" t
      _ -> throwException $ NotAConstructor "Literal" t

instance Unquote Term where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [] ->
        choice
          [(c `isCon` primAgdaTermUnsupported, pure hackReifyToMeta)]
          (throwException $ BadConstructor "Term" "arity 0 and not the `unsupported' constructor" t)

      Con c [x] -> do
        choice
          [ (c `isCon` primAgdaTermSort,   Sort <$> unquoteN x)
          , (c `isCon` primAgdaTermLit,    Lit <$> unquoteN x) ]
          (throwException $ BadConstructor "Term" "bad constructor" t)

      Con c [x, y] ->
        choice
          [ (c `isCon` primAgdaTermVar,    Var    <$> (fromInteger <$> unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermCon,    Con    <$> unquoteN x <*> unquoteN y)
          , (c `isCon` primAgdaTermDef,    Def    <$> (ensureDef =<< unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermLam,    Lam    <$> (flip setHiding defaultArgInfo <$> unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermPi,     mkPi   <$> (domFromArg                    <$> unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermExtLam, ExtLam <$> unquoteN x <*> unquoteN y) ]
          (throwException $ BadConstructor "Term" "bad term constructor" t)
        where
          mkPi a (Abs "_" b) = Pi a (Abs x b)
            where x | 0 `freeIn` b = pickName (unDom a)
                    | otherwise    = "_"
          mkPi a b@Abs{} = Pi a b
          mkPi _ NoAbs{} = __IMPOSSIBLE__

      Con{} -> throwException $ BadConstructor "Term" "neither arity 0 nor 1 nor 2" t
      Lit{} -> throwException $ BadConstructor "Term" "unexpected literal" t
      _ -> throwException $ NotAConstructor "Term" t

instance Unquote Pattern where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [ (c `isCon` primAgdaPatAbsurd, pure (VarP "()"))
          , (c `isCon` primAgdaPatDot,    pure (DotP hackReifyToMeta))
          ] __IMPOSSIBLE__
      Con c [x] -> do
        choice
          [ (c `isCon` primAgdaPatVar,  VarP  <$> unquoteNString x)
          , (c `isCon` primAgdaPatProj, ProjP <$> unquoteN x)
          , (c `isCon` primAgdaPatLit,  LitP  <$> unquoteN x) ]
          __IMPOSSIBLE__
      Con c [x, y] -> do
        choice
          [ (c `isCon` primAgdaPatCon, flip ConP Nothing <$> unquoteN x <*> (map (fmap unnamed) <$> unquoteN y)) ]
          __IMPOSSIBLE__
      Con c _ -> throwException $ BadConstructor "Pattern" "neither arity 0 nor 1 nor 2" t
      _ -> throwException $ NotAConstructor "Pattern" t

data UnquotedFunDef = UnQFun Type [Clause]

instance Unquote Clause where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [x] -> do
        choice
          [ (c `isCon` primAgdaClauseAbsurd, mkClause Nothing <$> unquoteN x) ]
          __IMPOSSIBLE__
      Con c [x, y] -> do
        choice
          [ (c `isCon` primAgdaClauseClause, checkClause =<< mkClause . Just <$> unquoteN y <*> unquoteN x) ]
          __IMPOSSIBLE__
      Con c _ -> throwException $ BadConstructor "Clause" "neither arity 1 nor 2" t
      _ -> throwException $ NotAConstructor "Clause" t
    where
      mkClause :: Maybe Term -> [I.Arg Pattern] -> I.Clause
      mkClause b ps0 =
        Clause { clauseRange     = noRange
               , clauseTel       = dummyTel n'
               , clausePerm      = Perm n vs
               , namedClausePats = ps
               , clauseBody      = mkBody n b
               , clauseType      = Nothing
               , clauseCatchall  = False }
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

      checkClause :: I.Clause -> UnquoteM I.Clause
      checkClause cl@Clause{ clausePerm = Perm n vs , clauseBody = body } = do
        let freevs    = allVars $ freeVars $ fromMaybe __IMPOSSIBLE__ $ getBody body
            propervs  = Set.fromList $ map ((n-1)-) vs
            dottedvs  = Set.difference (Set.fromList [0..n-1]) propervs
            offending = Set.intersection freevs dottedvs
        Agda.TypeChecking.Monad.reportSDoc "tc.unquote.clause.dotvars" 30 $ vcat
          [ text $ "checkClause "
          , nest 2 $ text $ "free vars:      " ++ show freevs
          , nest 2 $ text $ "dotted vars:    " ++ show dottedvs
          , nest 2 $ text $ "offending vars: " ++ show offending
          ]
        if Set.null offending
          then return cl
          else throwException $ RhsUsesDottedVar (Set.toList offending) t

instance Unquote UnquotedFunDef where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [x, y] -> do
        choice
          [ (c `isCon` primAgdaFunDefCon, UnQFun <$> unquoteN x <*> unquoteN y) ]
          __IMPOSSIBLE__
      Con c _ -> throwException $ BadConstructor "Pattern" "not of arity 2" t
      _ -> throwException $ NotAConstructor "Pattern" t

reifyUnquoted :: Reify a e => a -> TCM e
reifyUnquoted = nowReifyingUnquoted . disableDisplayForms . withShowAllArguments . reify

