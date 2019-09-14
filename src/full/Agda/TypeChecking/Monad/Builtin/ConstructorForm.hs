{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | Revealing the top-level layer of constructors of literals (natural numbers and quoted terms).
module Agda.TypeChecking.Monad.Builtin.ConstructorForm
  ( constructorForm
  , constructorForm'
  , QuotedTermKit
  , getQuotedTermKit
  , quotedTermConstructorForm
  , quotedTermConstructorFormM
  ) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans
import Control.Monad.Trans.Maybe

import qualified Data.HashMap.Strict as HMap
import qualified Data.Map as Map
import Data.Maybe
import Data.Void

import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.DropArgs
import Agda.TypeChecking.Substitute

import Agda.Utils.FileName
import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Size

-- | Rewrite a literal to constructor form if possible.
constructorForm :: (HasBuiltins m, MonadTCEnv m, ReadTCState m) => Term -> m Term
constructorForm v =
  case v of
    Lit (LitNat r n)
      | n == 0    -> fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinZero
      | n > 0     -> do
        suc <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinSuc
        return $ suc `apply1` Lit (LitNat r $ n - 1)
      | otherwise -> pure v
    Lit (LitTerm _ q) -> quotedTermConstructorFormM q
    _ -> pure v

-- | Caution: Only does natural numbers!
constructorForm' :: Applicative m => m Term -> m Term -> Term -> m Term
constructorForm' pZero pSuc v =
  case v of
    Lit (LitNat r n)
      | n == 0    -> pZero
      | n > 0     -> (`apply1` Lit (LitNat r $ n - 1)) <$> pSuc
      | otherwise -> pure v
    _ -> pure v

data QuotedTermKit = QuotedTermKit
  { qkitState :: TCState
  , qkitEnv   :: TCEnv
  }

getQuotedTermKit :: (HasBuiltins m, MonadTCEnv m, ReadTCState m) => m QuotedTermKit
getQuotedTermKit = do
  qkitState <- getTCState
  qkitEnv   <- askTC
  pure QuotedTermKit{..}

-- | Do one level of quoting, revealing the top-level reflected constructor.
quotedTermConstructorFormM :: (HasBuiltins m, MonadTCEnv m, ReadTCState m) => QuotedTerm -> m Term
quotedTermConstructorFormM q = do
  kit <- getQuotedTermKit
  pure $ quotedTermConstructorForm kit q

newtype QuoteKitM a = QuoteKitM { unQuoteKitM :: Reader QuotedTermKit a }
  deriving (Functor, Applicative, Monad)

instance ReadTCState QuoteKitM where
  getTCState = QuoteKitM $ asks qkitState
  locallyTCState l f (QuoteKitM m) = QuoteKitM $ local (\ q -> q { qkitState = over l f (qkitState q) }) m

instance MonadTCEnv QuoteKitM where
  askTC = QuoteKitM $ asks qkitEnv
  localTC f (QuoteKitM m) = QuoteKitM $ local (\ q -> q { qkitEnv = f (qkitEnv q) }) m

instance HasBuiltins QuoteKitM where
  getBuiltinThing b = do
    st <- getTCState
    return $ Map.lookup b $ Map.union (st ^. stLocalBuiltins) (st ^. stImportedBuiltins)

quotedTermConstructorForm :: QuotedTermKit -> QuotedTerm -> Term
quotedTermConstructorForm kit@QuotedTermKit{..} q = quoteTerm (quotedTerm q)
  where
    runQ :: QuoteKitM a -> a
    runQ m = runReader (unQuoteKitM m) kit

    getB b = fromMaybe __IMPOSSIBLE__ $ runQ (getBuiltin' b)

    Just qkitCurrentFile = runQ $ asksTC envCurrentPath
    Just qkitLevels  = runQ builtinLevelKit'
    qkitHidden       = getB builtinHidden
    qkitInstance     = getB builtinInstance
    qkitVisible      = getB builtinVisible
    qkitRelevant     = getB builtinRelevant
    qkitIrrelevant   = getB builtinIrrelevant
    qkitArg          = getB builtinArgArg
    qkitArgInfo      = getB builtinArgArgInfo
    qkitAbs          = getB builtinAbsAbs
    qkitNil          = getB builtinNil
    qkitCons         = getB builtinCons
    qkitVar          = getB builtinAgdaTermVar
    qkitDef          = getB builtinAgdaTermDef
    qkitCon          = getB builtinAgdaTermCon
    qkitMeta         = getB builtinAgdaTermMeta
    qkitLam          = getB builtinAgdaTermLam
    qkitPatLam       = getB builtinAgdaTermExtLam
    qkitPi           = getB builtinAgdaTermPi
    qkitSort         = getB builtinAgdaTermSort
    qkitLit          = getB builtinAgdaTermLit
    qkitUnknown      = getB builtinAgdaTermUnsupported
    qkitSortLit      = getB builtinAgdaSortLit
    qkitSortSet      = getB builtinAgdaSortSet
    qkitSortUnknown  = getB builtinAgdaSortUnsupported
    qkitVarP         = getB builtinAgdaPatVar
    qkitConP         = getB builtinAgdaPatCon
    qkitLitP         = getB builtinAgdaPatLit
    qkitProjP        = getB builtinAgdaPatProj
    qkitDotP         = getB builtinAgdaPatDot
    qkitAbsurdP      = getB builtinAgdaPatAbsurd
    qkitLitNat       = getB builtinAgdaLitNat
    qkitLitWord64    = getB builtinAgdaLitWord64
    qkitLitFloat     = getB builtinAgdaLitFloat
    qkitLitChar      = getB builtinAgdaLitChar
    qkitLitString    = getB builtinAgdaLitString
    qkitLitQName     = getB builtinAgdaLitQName
    qkitLitMeta      = getB builtinAgdaLitMeta
    qkitClause       = getB builtinAgdaClauseClause
    qkitAbsurdClause = getB builtinAgdaClauseAbsurd

    constInfo = flip HMap.lookup defs
      where
        defs  = HMap.union (qkitState ^. (stSignature . sigDefinitions))
                           (qkitState ^. (stImports   . sigDefinitions))

    quoteTerm v = case unSpine v of

      Def f es     ->
        case constInfo f of
          Just defn ->
            case defn of
              -- Pattern lambda
              Defn{theDef = Function{funExtLam = Just (ExtLamInfo m _), funClauses = cs}}
                | not $ null conOrProjPars -> __IMPOSSIBLE__ -- A pattern lambda should not have any extra parameters!
                | otherwise                ->
                  qkitPatLam $* [list $ map (quoteClause . (`applyE` pars)) cs, quoteArgs args]
                where
                  n            = size $ runQ $ lookupSection m
                  (pars, args) = splitAt n es
              Defn{theDef = Function{funCompiled = Just Fail, funClauses = [cl]}} ->
                -- Absurd lambda. See also corresponding code in InternalToAbstract.
                let n = length (namedClausePats cl) - 1 in
                qkitPatLam $* [list [quoteClause $ dropArgs n cl],
                               quoteArgs $ drop n es]
              _ -> qkitDef $* [litName f, list $ drop n $ conOrProjPars ++ quoteArgs' es]
                where
                  n = runQ $ getDefFreeVars f
            where
              -- #2220: remember to restore dropped parameters
              conOrProjPars = quoteParams defn
          Nothing -> qkitDef $* [litName f, quoteArgs es]

      Con ch ci es
        | isJust $ allApplyElims es -> qkitCon $* [litName c, args]
        | otherwise                 -> qkitUnknown
        where
          c         = conName ch
          Just cDef = constInfo c
          n         = runQ $ getDefFreeVars c
          args      = list $ drop n $ quoteParams cDef ++ quoteArgs' es

      Var x es     -> qkitVar  $* [Lit (LitNat noRange $ fromIntegral x), quoteArgs es]
      MetaV m es   -> qkitMeta $* [Lit (LitMeta noRange qkitCurrentFile m), quoteArgs es]
      Lit l        -> quoteLit l
      Lam h b      -> qkitLam  $* [quoteHiding (getHiding h), quoteAbs quoteTerm b]
      Pi a b       -> qkitPi   $* [quoteDom (quoteType <$> a), quoteAbs quoteType b]
      Sort s       -> qkitSort $* [quoteSort s]
      Level l      -> quoteTerm (unlevelWithKit qkitLevels l)
      DontCare t   -> qkitUnknown
      Dummy{}      -> __IMPOSSIBLE__

    quoteType = quoteTerm . unEl

    quoteHiding :: Hiding -> Term
    quoteHiding Hidden     = qkitHidden
    quoteHiding Instance{} = qkitInstance
    quoteHiding NotHidden  = qkitVisible

    quoteRelevance :: Relevance -> Term
    quoteRelevance Relevant   = qkitRelevant
    quoteRelevance Irrelevant = qkitIrrelevant
    quoteRelevance NonStrict  = qkitRelevant

    -- TODO: quote Quanity
    quoteArgInfo :: ArgInfo -> Term
    quoteArgInfo (ArgInfo h m _ _) =
      qkitArgInfo $* [quoteHiding h, quoteRelevance (getRelevance m)]

    quoteArg :: Arg Term -> Term
    quoteArg (Arg info t) = qkitArg $* [quoteArgInfo info, t]

    quoteDom :: Dom Term -> Term
    quoteDom Dom{domInfo = info, unDom = t} = qkitArg $* [quoteArgInfo info, t]

    quoteAbs :: Subst t a => (a -> Term) -> Abs a -> Term
    quoteAbs q (Abs s t)   = qkitAbs $* [Lit (LitString noRange s), q t]
    quoteAbs q (NoAbs s t) = qkitAbs $* [Lit (LitString noRange s), q (raise 1 t)]

    quoteArgs :: Elims -> Term
    quoteArgs = list . quoteArgs'

    quoteArgs' :: Elims -> [Term]
    quoteArgs' es = map (quoteArg . fmap quoted) vs
      where vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es

    quoteLit :: Literal' QuotedTerm -> Term
    quoteLit l@LitNat{}    = qkitLit $$ (qkitLitNat    $$ Lit l)
    quoteLit l@LitWord64{} = qkitLit $$ (qkitLitWord64 $$ Lit l)
    quoteLit l@LitFloat{}  = qkitLit $$ (qkitLitFloat  $$ Lit l)
    quoteLit l@LitChar{}   = qkitLit $$ (qkitLitChar   $$ Lit l)
    quoteLit l@LitString{} = qkitLit $$ (qkitLitString $$ Lit l)
    quoteLit l@LitQName{}  = qkitLit $$ (qkitLitQName  $$ Lit l)
    quoteLit l@LitMeta {}  = qkitLit $$ (qkitLitMeta   $$ Lit l)
    quoteLit (LitTerm _ q) = quoteTerm $ quoteTerm $ quotedTerm q

    quoteSortLevelTerm :: Level -> Term
    quoteSortLevelTerm (Max [])              = qkitSortLit $$ Lit (LitNat noRange 0)
    quoteSortLevelTerm (Max [ClosedLevel n]) = qkitSortLit $$ Lit (LitNat noRange n)
    quoteSortLevelTerm l                     = qkitSortSet $$ quoteTerm (unlevelWithKit qkitLevels l)

    quoteSort :: Sort -> Term
    quoteSort (Type t)     = quoteSortLevelTerm t
    quoteSort Prop{}       = qkitSortUnknown
    quoteSort Inf          = qkitSortUnknown
    quoteSort SizeUniv     = qkitSortUnknown
    quoteSort PiSort{}     = qkitSortUnknown
    quoteSort UnivSort{}   = qkitSortUnknown
    quoteSort (MetaS x es) = quoteTerm $ MetaV x es
    quoteSort (DefS d es)  = quoteTerm $ Def d es
    quoteSort DummyS{}     =__IMPOSSIBLE__

    quotePats :: [NamedArg DeBruijnPattern] -> Term
    quotePats ps = list $ map (quoteArg . fmap (quotePat . namedThing)) ps

    quotePat :: DeBruijnPattern -> Term
    quotePat p
     | patternOrigin p == Just PatOAbsurd = qkitAbsurdP
    quotePat (VarP o x)        = qkitVarP $$ litString (dbPatVarName x)
    quotePat (DotP _ _)        = qkitDotP
    quotePat (ConP c _ ps)     = qkitConP $* [litName (conName c), quotePats ps]
    quotePat (LitP l)          = qkitLitP $$ quoteLit (vacuous l)
    quotePat (ProjP _ x)       = qkitProjP $$ litName x
    quotePat (IApplyP o t u x) = qkitDotP   -- TODO!
    quotePat DefP{}            = __IMPOSSIBLE__

    litString = Lit . LitString noRange
    litName   = Lit . LitQName  noRange
    litNat    = Lit . LitNat    noRange

    quoteClause :: Clause -> Term
    quoteClause cl@Clause{namedClausePats = ps, clauseBody = body} =
      case body of
        Nothing -> qkitAbsurdClause $$ quotePats ps
        Just b  -> qkitClause $* [quotePats ps, quoteTerm v]
          where
            perm = fromMaybe __IMPOSSIBLE__ $ dbPatPerm' False ps -- Dot patterns don't count (#2203)
            v    = applySubst (renamingR perm) b

    quoteParams :: Definition -> [Term]
    quoteParams def = map (quoteArg . (qkitUnknown <$) . argFromDom) $ take np $ telToList tel
      where
        np = case theDef def of
               Constructor{ conPars = np }        -> np
               Function{ funProjection = Just p } -> projIndex p - 1
               _                                  -> 0
        TelV tel _ = telView' (defType def)

    list :: [Term] -> Term
    list = foldr (\ a as -> qkitCons $* [a, as]) qkitNil

    ($*) :: Apply a => a -> [Term] -> a
    ($*) = applys

    ($$) :: Apply a => a -> Term -> a
    ($$) = apply1

    quoted :: Term -> Term
    quoted v = Lit $ LitTerm noRange $ QuotedTerm Nothing v Nothing


