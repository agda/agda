
module Agda.TypeChecking.Quote where

import Control.Arrow ((&&&))
import Control.Monad

import Data.Maybe (fromMaybe)

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern ( dbPatPerm' )
import Agda.Syntax.Literal
import Agda.Syntax.Position

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.DropArgs
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Substitute

import Agda.Utils.Impossible
import Agda.Utils.FileName
import Agda.Utils.Size


data QuotingKit = QuotingKit
  { quoteTermWithKit   :: Term       -> ReduceM Term
  , quoteTypeWithKit   :: Type       -> ReduceM Term
  , quoteClauseWithKit :: Clause     -> ReduceM Term
  , quoteDomWithKit    :: Dom Type   -> ReduceM Term
  , quoteDefnWithKit   :: Definition -> ReduceM Term
  , quoteListWithKit   :: forall a. (a -> ReduceM Term) -> [a] -> ReduceM Term
  }

quotingKit :: TCM QuotingKit
quotingKit = do
  currentFile     <- fromMaybe __IMPOSSIBLE__ <$> asksTC envCurrentPath
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
  meta            <- primAgdaTermMeta
  lit             <- primAgdaTermLit
  litNat          <- primAgdaLitNat
  litWord64       <- primAgdaLitNat
  litFloat        <- primAgdaLitFloat
  litChar         <- primAgdaLitChar
  litString       <- primAgdaLitString
  litQName        <- primAgdaLitQName
  litMeta         <- primAgdaLitMeta
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
  Con z _ _       <- primZero
  Con s _ _       <- primSuc
  unsupported     <- primAgdaTermUnsupported

  agdaDefinitionFunDef          <- primAgdaDefinitionFunDef
  agdaDefinitionDataDef         <- primAgdaDefinitionDataDef
  agdaDefinitionRecordDef       <- primAgdaDefinitionRecordDef
  agdaDefinitionPostulate       <- primAgdaDefinitionPostulate
  agdaDefinitionPrimitive       <- primAgdaDefinitionPrimitive
  agdaDefinitionDataConstructor <- primAgdaDefinitionDataConstructor

  let (@@) :: Apply a => ReduceM a -> ReduceM Term -> ReduceM a
      t @@ u = apply <$> t <*> ((:[]) . defaultArg <$> u)

      (!@) :: Apply a => a -> ReduceM Term -> ReduceM a
      t !@ u = pure t @@ u

      (!@!) :: Apply a => a -> Term -> ReduceM a
      t !@! u = pure t @@ pure u

      quoteHiding :: Hiding -> ReduceM Term
      quoteHiding Hidden     = pure hidden
      quoteHiding Instance{} = pure instanceH
      quoteHiding NotHidden  = pure visible

      quoteRelevance :: Relevance -> ReduceM Term
      quoteRelevance Relevant   = pure relevant
      quoteRelevance Irrelevant = pure irrelevant
      quoteRelevance NonStrict  = pure relevant

      -- TODO: quote Quanity
      quoteArgInfo :: ArgInfo -> ReduceM Term
      quoteArgInfo (ArgInfo h m _ _) =
        arginfo !@ quoteHiding h @@ quoteRelevance (getRelevance m)

      quoteLit :: Literal -> ReduceM Term
      quoteLit l@LitNat{}    = litNat    !@! Lit l
      quoteLit l@LitWord64{} = litWord64 !@! Lit l
      quoteLit l@LitFloat{}  = litFloat  !@! Lit l
      quoteLit l@LitChar{}   = litChar   !@! Lit l
      quoteLit l@LitString{} = litString !@! Lit l
      quoteLit l@LitQName{}  = litQName  !@! Lit l
      quoteLit l@LitMeta {}  = litMeta   !@! Lit l

      -- We keep no ranges in the quoted term, so the equality on terms
      -- is only on the structure.
      quoteSortLevelTerm :: Level -> ReduceM Term
      quoteSortLevelTerm (Max [])              = setLit !@! Lit (LitNat noRange 0)
      quoteSortLevelTerm (Max [ClosedLevel n]) = setLit !@! Lit (LitNat noRange n)
      quoteSortLevelTerm l                     = set !@ quoteTerm (unlevelWithKit lkit l)

      quoteSort :: Sort -> ReduceM Term
      quoteSort (Type t) = quoteSortLevelTerm t
      quoteSort Prop{}   = pure unsupportedSort
      quoteSort Inf      = pure unsupportedSort
      quoteSort SizeUniv = pure unsupportedSort
      quoteSort PiSort{} = pure unsupportedSort
      quoteSort UnivSort{}   = pure unsupportedSort
      quoteSort (MetaS x es) = quoteTerm $ MetaV x es
      quoteSort (DefS d es)  = quoteTerm $ Def d es
      quoteSort (DummyS s)   =__IMPOSSIBLE_VERBOSE__ s

      quoteType :: Type -> ReduceM Term
      quoteType (El _ t) = quoteTerm t

      quoteQName :: QName -> ReduceM Term
      quoteQName x = pure $ Lit $ LitQName noRange x

      quotePats :: [NamedArg DeBruijnPattern] -> ReduceM Term
      quotePats ps = list $ map (quoteArg quotePat . fmap namedThing) ps

      quotePat :: DeBruijnPattern -> ReduceM Term
      quotePat p
       | patternOrigin p == Just PatOAbsurd = pure absurdP
      quotePat (VarP o x)        = varP !@! quoteString (dbPatVarName x)
      quotePat (DotP _ _)        = pure dotP
      quotePat (ConP c _ ps)     = conP !@ quoteQName (conName c) @@ quotePats ps
      quotePat (LitP l)          = litP !@ quoteLit l
      quotePat (ProjP _ x)       = projP !@ quoteQName x
      quotePat (IApplyP o t u x) = pure unsupported
      quotePat DefP{}            = pure unsupported

      quoteClause :: Clause -> ReduceM Term
      quoteClause cl@Clause{namedClausePats = ps, clauseBody = body} =
        case body of
          Nothing -> absurdClause !@ quotePats ps
          Just b  ->
            let perm = fromMaybe __IMPOSSIBLE__ $ dbPatPerm' False ps -- Dot patterns don't count (#2203)
                v    = applySubst (renamingR perm) b
            in normalClause !@ quotePats ps @@ quoteTerm v

      list :: [ReduceM Term] -> ReduceM Term
      list = foldr (\ a as -> cons !@ a @@ as) (pure nil)

      quoteList :: (a -> ReduceM Term) -> [a] -> ReduceM Term
      quoteList q xs = list (map q xs)

      quoteDom :: (Type -> ReduceM Term) -> Dom Type -> ReduceM Term
      quoteDom q Dom{domInfo = info, unDom = t} = arg !@ quoteArgInfo info @@ q t

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
             in  var !@! Lit (LitNat noRange $ fromIntegral n) @@ quoteArgs ts
          Lam info t -> lam !@ quoteHiding (getHiding info) @@ quoteAbs quoteTerm t
          Def x es   -> do
            defn <- getConstInfo x
            -- #2220: remember to restore dropped parameters
            let
              conOrProjPars = defParameters defn
              ts = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
              qx Function{ funExtLam = Just (ExtLamInfo m _), funClauses = cs } = do
                    -- An extended lambda should not have any extra parameters!
                    unless (null conOrProjPars) __IMPOSSIBLE__
                    n <- size <$> lookupSection m
                    let (pars, args) = splitAt n ts
                    extlam !@ list (map (quoteClause . (`apply` pars)) cs)
                           @@ list (map (quoteArg quoteTerm) args)
              qx df@Function{ funCompiled = Just Fail, funClauses = [cl] } = do
                    -- See also corresponding code in InternalToAbstract
                    let n = length (namedClausePats cl) - 1
                    extlam !@ list [quoteClause $ dropArgs n cl]
                           @@ list (drop n $ map (quoteArg quoteTerm) ts)
              qx _ = do
                n <- getDefFreeVars x
                def !@! quoteName x
                     @@ list (drop n $ conOrProjPars ++ map (quoteArg quoteTerm) ts)
            qx (theDef defn)
          Con x ci es | Just ts <- allApplyElims es -> do
            cDef <- getConstInfo (conName x)
            n    <- getDefFreeVars (conName x)
            let args = list $ drop n $ defParameters cDef ++ map (quoteArg quoteTerm) ts
            con !@! quoteConName x @@ args
          Con x ci es -> pure unsupported
          Pi t u     -> pi !@  quoteDom quoteType t
                            @@ quoteAbs quoteType u
          Level l    -> quoteTerm (unlevelWithKit lkit l)
          Lit l      -> lit !@ quoteLit l
          Sort s     -> sort !@ quoteSort s
          MetaV x es -> meta !@! quoteMeta currentFile x @@ quoteArgs vs
            where vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
          DontCare{} -> pure unsupported -- could be exposed at some point but we have to take care
          Dummy s _  -> __IMPOSSIBLE_VERBOSE__ s

      defParameters :: Definition -> [ReduceM Term]
      defParameters def = map par hiding
        where
          np = case theDef def of
                 Constructor{ conPars = np }        -> np
                 Function{ funProjection = Just p } -> projIndex p - 1
                 _                                  -> 0
          TelV tel _ = telView' (defType def)
          hiding     = map (getHiding &&& getRelevance) $ take np $ telToList tel
          par (h, r) = arg !@ (arginfo !@ quoteHiding h @@ quoteRelevance r) @@ pure unsupported

      quoteDefn :: Definition -> ReduceM Term
      quoteDefn def =
        case theDef def of
          Function{funClauses = cs} ->
            agdaDefinitionFunDef !@ quoteList quoteClause cs
          Datatype{dataPars = np, dataCons = cs} ->
            agdaDefinitionDataDef !@! quoteNat (fromIntegral np) @@ quoteList (pure . quoteName) cs
          Record{recConHead = c, recFields = fs} ->
            agdaDefinitionRecordDef
              !@! quoteName (conName c)
              @@ quoteList (quoteArg (pure . quoteName)) fs
          Axiom{}       -> pure agdaDefinitionPostulate
          DataOrRecSig{} -> pure agdaDefinitionPostulate
          GeneralizableVar{} -> pure agdaDefinitionPostulate  -- TODO: reflect generalizable vars
          AbstractDefn{}-> pure agdaDefinitionPostulate
          Primitive{primClauses = cs} | not $ null cs ->
            agdaDefinitionFunDef !@ quoteList quoteClause cs
          Primitive{}   -> pure agdaDefinitionPrimitive
          Constructor{conData = d} ->
            agdaDefinitionDataConstructor !@! quoteName d

  return $ QuotingKit quoteTerm quoteType quoteClause (quoteDom quoteType) quoteDefn quoteList

quoteString :: String -> Term
quoteString = Lit . LitString noRange

quoteName :: QName -> Term
quoteName x = Lit (LitQName noRange x)

quoteNat :: Integer -> Term
quoteNat n
  | n >= 0    = Lit (LitNat noRange n)
  | otherwise = __IMPOSSIBLE__

quoteConName :: ConHead -> Term
quoteConName = quoteName . conName

quoteMeta :: AbsolutePath -> MetaId -> Term
quoteMeta file = Lit . LitMeta noRange file

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

quoteDefn :: Definition -> TCM Term
quoteDefn def = do
  kit <- quotingKit
  runReduceM (quoteDefnWithKit kit def)

quoteList :: [Term] -> TCM Term
quoteList xs = do
  kit <- quotingKit
  runReduceM (quoteListWithKit kit pure xs)
