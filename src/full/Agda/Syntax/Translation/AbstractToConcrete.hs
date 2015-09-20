{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

-- {-# OPTIONS -fwarn-unused-binds #-}

{-| The translation of abstract syntax to concrete syntax has two purposes.
    First it allows us to pretty print abstract syntax values without having to
    write a dedicated pretty printer, and second it serves as a sanity check
    for the concrete to abstract translation: translating from concrete to
    abstract and then back again should be (more or less) the identity.
-}
module Agda.Syntax.Translation.AbstractToConcrete
    ( ToConcrete(..)
    , toConcreteCtx
    , abstractToConcrete_
    , abstractToConcreteEnv
    , runAbsToCon
    , RangeAndPragma(..)
    , abstractToConcreteCtx
    , withScope
    , makeEnv
    , AbsToCon, DontTouchMe, Env
    , noTakenNames
    ) where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Control.Monad.Reader

import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (traverse)

import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Info
import Agda.Syntax.Internal (MetaId(..))
import Agda.Syntax.Fixity
import Agda.Syntax.Concrete as C
import Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views as AV
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Monad.State (getScope)
import Agda.TypeChecking.Monad.Base  (TCM, NamedMeta(..))
import Agda.TypeChecking.Monad.Options

import qualified Agda.Utils.AssocList as AssocList
import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Tuple
import Agda.Utils.Pretty (prettyShow)

#include "undefined.h"
import Agda.Utils.Impossible

-- Environment ------------------------------------------------------------

data Env = Env { takenNames   :: Set C.Name
               , currentScope :: ScopeInfo
               }

defaultEnv :: Env
defaultEnv = Env { takenNames   = Set.empty
                 , currentScope = emptyScopeInfo
                 }

makeEnv :: ScopeInfo -> Env
makeEnv scope = Env { takenNames   = Set.union vars defs
                    , currentScope = scope
                    }
  where
    vars  = Set.fromList $ map fst $ scopeLocals scope
    defs  = Map.keysSet $ nsNames $ everythingInScope scope

currentPrecedence :: AbsToCon Precedence
currentPrecedence = asks $ scopePrecedence . currentScope

withPrecedence :: Precedence -> AbsToCon a -> AbsToCon a
withPrecedence p = local $ \e ->
  e { currentScope = (currentScope e) { scopePrecedence = p } }

withScope :: ScopeInfo -> AbsToCon a -> AbsToCon a
withScope scope = local $ \e -> e { currentScope = scope }

noTakenNames :: AbsToCon a -> AbsToCon a
noTakenNames = local $ \e -> e { takenNames = Set.empty }

-- The Monad --------------------------------------------------------------

-- | We put the translation into TCM in order to print debug messages.
type AbsToCon = ReaderT Env TCM

runAbsToCon :: AbsToCon c -> TCM c
runAbsToCon m = do
  scope <- getScope
  runReaderT m (makeEnv scope)

abstractToConcreteEnv :: ToConcrete a c => Env -> a -> TCM c
abstractToConcreteEnv flags a = runReaderT (toConcrete a) flags

abstractToConcreteCtx :: ToConcrete a c => Precedence -> a -> TCM c
abstractToConcreteCtx ctx x = do
  scope <- getScope
  let scope' = scope { scopePrecedence = ctx }
  abstractToConcreteEnv (makeEnv scope') x

abstractToConcrete_ :: ToConcrete a c => a -> TCM c
abstractToConcrete_ = runAbsToCon . toConcrete

-- Dealing with names -----------------------------------------------------

-- | Names in abstract syntax are fully qualified, but the concrete syntax
--   requires non-qualified names in places. In theory (if all scopes are
--   correct), we should get a non-qualified name when translating back to a
--   concrete name, but I suspect the scope isn't always perfect. In these
--   cases we just throw away the qualified part. It's just for pretty printing
--   anyway...
unsafeQNameToName :: C.QName -> C.Name
unsafeQNameToName = C.unqualify

lookupName :: A.Name -> AbsToCon C.Name
lookupName x = do
  names <- asks $ scopeLocals . currentScope
  case lookup x $ mapMaybe (\ (c,x) -> (,c) <$> notShadowedLocal x) names of
      Just y  -> return y
      Nothing -> return $ nameConcrete x

lookupQName :: AllowAmbiguousConstructors -> A.QName -> AbsToCon C.QName
lookupQName ambCon x = do
  ys <- inverseScopeLookupName' ambCon x <$> asks currentScope
  lift $ reportSLn "scope.inverse" 100 $
    "inverse looking up abstract name " ++ show x ++ " yields " ++ show ys
  case ys of
    (y : _) -> return y
    [] -> do
      let y = qnameToConcrete x
      if isUnderscore y
        then return y
        else return $ C.Qual (C.Name noRange [Id empty]) y
        -- this is what happens for names that are not in scope (private names)

lookupModule :: A.ModuleName -> AbsToCon C.QName
lookupModule x =
    do  scope <- asks currentScope
        case inverseScopeLookupModule x scope of
            (y : _) -> return y
            []      -> return $ mnameToConcrete x
                -- this is what happens for names that are not in scope (private names)

bindName :: A.Name -> (C.Name -> AbsToCon a) -> AbsToCon a
bindName x ret = do
  names <- asks takenNames
  let y = nameConcrete x
  case (Set.member y names) of
    _ | isNoName y -> ret y
    True           -> bindName (nextName x) ret
    False          ->
        local (\e -> e { takenNames   = Set.insert y $ takenNames e
                       , currentScope = (`updateScopeLocals` currentScope e) $
                           AssocList.insert y (LocalVar x)
                       }
              ) $ ret y

-- Dealing with precedences -----------------------------------------------

-- | General bracketing function.
bracket' ::    (e -> e)             -- ^ the bracketing function
            -> (Precedence -> Bool) -- ^ Should we bracket things
                                    --   which have the given
                                    --   precedence?
            -> e -> AbsToCon e
bracket' paren needParen e =
    do  p <- currentPrecedence
        return $ if needParen p then paren e else e

-- | Expression bracketing
bracket :: (Precedence -> Bool) -> AbsToCon C.Expr -> AbsToCon C.Expr
bracket par m =
    do  e <- m
        bracket' (Paren (getRange e)) par e

-- | Pattern bracketing
bracketP_ :: (Precedence -> Bool) -> AbsToCon C.Pattern -> AbsToCon C.Pattern
bracketP_ par m =
    do  e <- m
        bracket' (ParenP (getRange e)) par e

{- UNUSED
-- | Pattern bracketing
bracketP :: (Precedence -> Bool) -> (C.Pattern -> AbsToCon a)
                                 -> ((C.Pattern -> AbsToCon a) -> AbsToCon a)
                                 -> AbsToCon a
bracketP par ret m = m $ \p -> do
    p <- bracket' (ParenP $ getRange p) par p
    ret p
-}

-- Dealing with infix declarations ----------------------------------------

-- | If a name is defined with a fixity that differs from the default, we have
--   to generate a fixity declaration for that name.
withInfixDecl :: DefInfo -> C.Name -> AbsToCon [C.Declaration] -> AbsToCon [C.Declaration]
withInfixDecl i x m = do
  ds <- m
  return $ fixDecl ++ synDecl ++ ds
 where fixDecl = [C.Infix (theFixity $ defFixity i) [x] | theFixity (defFixity i) /= noFixity]
       synDecl = [C.Syntax x (theNotation (defFixity i))]

{- UNUSED
withInfixDecls :: [(DefInfo, C.Name)] -> AbsToCon [C.Declaration] -> AbsToCon [C.Declaration]
withInfixDecls = foldr (.) id . map (uncurry withInfixDecl)
-}

-- Dealing with private definitions ---------------------------------------

withAbstractPrivate :: DefInfo -> AbsToCon [C.Declaration] -> AbsToCon [C.Declaration]
withAbstractPrivate i m =
    case (defAccess i, defAbstract i) of
        (PublicAccess, ConcreteDef) -> m
        (p,a)                       ->
            do  ds <- m
                return $ abst a $ priv p $ ds
    where
        priv PrivateAccess ds = [ C.Private (getRange ds) ds ]
        priv _ ds             = ds
        abst AbstractDef ds   = [ C.Abstract (getRange ds) ds ]
        abst _ ds             = ds

-- The To Concrete Class --------------------------------------------------

class ToConcrete a c | a -> c where
    toConcrete :: a -> AbsToCon c
    bindToConcrete :: a -> (c -> AbsToCon b) -> AbsToCon b

    toConcrete     x     = bindToConcrete x return
    bindToConcrete x ret = ret =<< toConcrete x

-- | Translate something in a context of the given precedence.
toConcreteCtx :: ToConcrete a c => Precedence -> a -> AbsToCon c
toConcreteCtx p x = withPrecedence p $ toConcrete x

-- | Translate something in a context of the given precedence.
bindToConcreteCtx :: ToConcrete a c => Precedence -> a -> (c -> AbsToCon b) -> AbsToCon b
bindToConcreteCtx p x ret = withPrecedence p $ bindToConcrete x ret

-- | Translate something in the top context.
toConcreteTop :: ToConcrete a c => a -> AbsToCon c
toConcreteTop = toConcreteCtx TopCtx

-- | Translate something in the top context.
bindToConcreteTop :: ToConcrete a c => a -> (c -> AbsToCon b) -> AbsToCon b
bindToConcreteTop = bindToConcreteCtx TopCtx

-- | Translate something in a context indicated by 'Hiding' info.
toConcreteHiding :: (LensHiding h, ToConcrete a c) => h -> a -> AbsToCon c
toConcreteHiding h =
  case getHiding h of
    NotHidden -> toConcrete
    Hidden    -> toConcreteTop
    Instance  -> toConcreteTop

-- | Translate something in a context indicated by 'Hiding' info.
bindToConcreteHiding :: (LensHiding h, ToConcrete a c) => h -> a -> (c -> AbsToCon b) -> AbsToCon b
bindToConcreteHiding h =
  case getHiding h of
    NotHidden -> bindToConcrete
    Hidden    -> bindToConcreteTop
    Instance  -> bindToConcreteTop

-- General instances ------------------------------------------------------

instance ToConcrete a c => ToConcrete [a] [c] where
    toConcrete     = mapM toConcrete
    bindToConcrete = thread bindToConcrete

instance (ToConcrete a1 c1, ToConcrete a2 c2) => ToConcrete (Either a1 a2) (Either c1 c2) where
    toConcrete = traverseEither toConcrete toConcrete
    bindToConcrete (Left x) ret =
        bindToConcrete x $ \x ->
        ret (Left x)
    bindToConcrete (Right y) ret =
        bindToConcrete y $ \y ->
        ret (Right y)

instance (ToConcrete a1 c1, ToConcrete a2 c2) => ToConcrete (a1,a2) (c1,c2) where
    toConcrete (x,y) = liftM2 (,) (toConcrete x) (toConcrete y)
    bindToConcrete (x,y) ret =
        bindToConcrete x $ \x ->
        bindToConcrete y $ \y ->
        ret (x,y)

instance (ToConcrete a1 c1, ToConcrete a2 c2, ToConcrete a3 c3) =>
         ToConcrete (a1,a2,a3) (c1,c2,c3) where
    toConcrete (x,y,z) = reorder <$> toConcrete (x,(y,z))
        where
            reorder (x,(y,z)) = (x,y,z)

    bindToConcrete (x,y,z) ret = bindToConcrete (x,(y,z)) $ ret . reorder
        where
            reorder (x,(y,z)) = (x,y,z)

instance ToConcrete (Common.ArgInfo ac) C.ArgInfo where
  toConcrete info = -- do cs <- mapM toConcrete $ argInfoColors info
                    return $ info { argInfoColors = [] } -- TODO: zapping ignoring colours

instance ToConcrete a c => ToConcrete (Common.Arg ac a) (C.Arg c) where
    toConcrete (Common.Arg info x) = Common.Arg
      <$> toConcrete info
      <*> toConcreteHiding info x

    bindToConcrete (Common.Arg info x) ret = do
      info <- toConcrete info
      bindToConcreteCtx (hiddenArgumentCtx $ getHiding info) x $
        ret . Common.Arg info

instance ToConcrete a c => ToConcrete (WithHiding a) (WithHiding c) where
  toConcrete     (WithHiding h a) = WithHiding h <$> toConcreteHiding h a
  bindToConcrete (WithHiding h a) ret = bindToConcreteHiding h a $ \ a ->
    ret $ WithHiding h a

instance ToConcrete a c => ToConcrete (Named name a) (Named name c) where
    toConcrete (Named n x) = Named n <$> toConcrete x
    bindToConcrete (Named n x) ret = bindToConcrete x $ ret . Named n

newtype DontTouchMe a = DontTouchMe a

instance ToConcrete (DontTouchMe a) a where
    toConcrete (DontTouchMe x) = return x

-- Names ------------------------------------------------------------------

instance ToConcrete A.Name C.Name where
  toConcrete       = lookupName
  bindToConcrete x = bindName x

instance ToConcrete A.QName C.QName where
  toConcrete = lookupQName AllowAmbiguousConstructors

instance ToConcrete A.ModuleName C.QName where
  toConcrete = lookupModule

-- Expression instance ----------------------------------------------------

instance ToConcrete A.Expr C.Expr where
    toConcrete (Var x)            = Ident . C.QName <$> toConcrete x
    toConcrete (Def x)            = Ident <$> toConcrete x
    toConcrete (Proj x)           = Ident <$> toConcrete x
    toConcrete (A.Macro x)        = Ident <$> toConcrete x
    toConcrete (Con (AmbQ (x:_))) = Ident <$> toConcrete x
    toConcrete (Con (AmbQ []))    = __IMPOSSIBLE__
        -- for names we have to use the name from the info, since the abstract
        -- name has been resolved to a fully qualified name (except for
        -- variables)
    toConcrete (A.Lit (LitQName r x)) = do
      x <- lookupQName NoAmbiguousConstructors x
      bracket appBrackets $ return $
        C.App r (C.Quote r) (defaultNamedArg $ C.Ident x)
    toConcrete (A.Lit l)            = return $ C.Lit l

    -- Andreas, 2014-05-17  We print question marks with their
    -- interaction id, in case @metaNumber /= Nothing@
    toConcrete (A.QuestionMark i ii)= return $
      C.QuestionMark (getRange i) $
        interactionId ii <$ metaNumber i

    toConcrete (A.Underscore i)     = return $
      C.Underscore (getRange i) $
        prettyShow . NamedMeta (metaNameSuggestion i) . MetaId <$> metaNumber i

    toConcrete e@(A.App i e1 e2)    =
        tryToRecoverOpApp e
        -- or fallback to App
        $ bracket appBrackets
        $ do e1' <- toConcreteCtx FunctionCtx e1
             e2' <- toConcreteCtx ArgumentCtx e2
             return $ C.App (getRange i) e1' e2'

    toConcrete (A.WithApp i e es) =
      bracket withAppBrackets $ do
        e <- toConcreteCtx WithFunCtx e
        es <- mapM (toConcreteCtx WithArgCtx) es
        return $ C.WithApp (getRange i) e es

    toConcrete (A.AbsurdLam i h) =
      bracket lamBrackets $ return $ C.AbsurdLam (getRange i) h
    toConcrete e@(A.Lam i _ _)      =
        bracket lamBrackets
        $ case lamView e of
            (bs, e) ->
                bindToConcrete (map makeDomainFree bs) $ \bs -> do
                    e  <- toConcreteTop e
                    return $ C.Lam (getRange i) (concat bs) e
        where
            lamView (A.Lam _ b@(A.DomainFree _ _) e) =
                case lamView e of
                    ([], e)                        -> ([b], e)
                    (bs@(A.DomainFree _ _ : _), e) -> (b:bs, e)
                    _                              -> ([b], e)
            lamView (A.Lam _ b@(A.DomainFull _) e) =
                case lamView e of
                    ([], e)                        -> ([b], e)
                    (bs@(A.DomainFull _ : _), e)   -> (b:bs, e)
                    _                              -> ([b], e)
            lamView e = ([], e)
    toConcrete (A.ExtendedLam i di qname cs) =
        bracket lamBrackets $ do
          decls <- concat <$> toConcrete cs
          let namedPat np = case getHiding np of
                 NotHidden -> namedArg np
                 Hidden    -> C.HiddenP noRange (unArg np)
                 Instance  -> C.InstanceP noRange (unArg np)
              -- we know all lhs are of the form `.extlam p1 p2 ... pn`,
              -- with the name .extlam leftmost. It is our mission to remove it.
          let removeApp (C.RawAppP r (_:es)) = return $ C.RawAppP r es
              removeApp (C.AppP (C.IdentP _) np) = return $ namedPat np
              removeApp (C.AppP p np) = do
                p <- removeApp p
                return $ C.AppP p np
              removeApp p = do
                lift $ reportSLn "extendedlambda" 50 $ "abstractToConcrete removeApp p = " ++ show p
                return p -- __IMPOSSIBLE__ -- Andreas, this is actually not impossible, my strictification exposed this sleeping bug
          let decl2clause (C.FunClause lhs rhs wh) = do
                let p = lhsOriginalPattern lhs
                lift $ reportSLn "extendedlambda" 50 $ "abstractToConcrete extended lambda pattern p = " ++ show p
                p' <- removeApp p
                lift $ reportSLn "extendedlambda" 50 $ "abstractToConcrete extended lambda pattern p' = " ++ show p'
                return (lhs{ lhsOriginalPattern = p' }, rhs, wh)
              decl2clause _ = __IMPOSSIBLE__
          C.ExtendedLam (getRange i) <$> mapM decl2clause decls
    toConcrete (A.Pi _ [] e) = toConcrete e
    toConcrete t@(A.Pi i _ _)  = case piTel t of
      (tel, e) ->
        bracket piBrackets
        $ bindToConcrete tel $ \b' -> do
             e' <- toConcreteTop e
             return $ C.Pi (concat b') e'
      where
        piTel (A.Pi _ tel e) = (tel ++) -*- id $ piTel e
        piTel e              = ([], e)

    toConcrete (A.Fun i a b) =
        bracket piBrackets
        $ do a' <- toConcreteCtx (if irr then DotPatternCtx else FunctionSpaceDomainCtx) a
             b' <- toConcreteTop b
             return $ C.Fun (getRange i) (addRel a' $ mkArg a') b'
        where
            irr        = getRelevance a `elem` [Irrelevant, NonStrict]
            addRel a e = case getRelevance a of
                           Irrelevant -> addDot a e
                           NonStrict  -> addDot a (addDot a e)
                           _          -> e
            addDot a e = Dot (getRange a) e
            mkArg (Common.Arg info e) = case getHiding info of
                                          Hidden    -> HiddenArg   (getRange e) (unnamed e)
                                          Instance  -> InstanceArg (getRange e) (unnamed e)
                                          NotHidden -> e

    toConcrete (A.Set i 0)  = return $ C.Set (getRange i)
    toConcrete (A.Set i n)  = return $ C.SetN (getRange i) n
    toConcrete (A.Prop i)   = return $ C.Prop (getRange i)

    toConcrete (A.Let i ds e) =
        bracket lamBrackets
        $ bindToConcrete ds $ \ds' -> do
             e'  <- toConcreteTop e
             return $ C.Let (getRange i) (concat ds') e'

    toConcrete (A.Rec i fs) =
      bracket appBrackets $ do
        C.Rec (getRange i) . map (fmap (\x -> ModuleAssignment x [] defaultImportDir)) <$> toConcreteTop fs

    toConcrete (A.RecUpdate i e fs) =
      bracket appBrackets $ do
        C.RecUpdate (getRange i) <$> toConcrete e <*> toConcreteTop fs

    toConcrete (A.ETel tel) = do
      tel <- concat <$> toConcrete tel
      return $ C.ETel tel

    toConcrete (A.ScopedExpr _ e) = toConcrete e

    toConcrete (A.QuoteGoal i x e) =
      bracket lamBrackets $
        bindToConcrete x $ \ x' -> do
            e' <- toConcrete e
            return $ C.QuoteGoal (getRange i) x' e'
    toConcrete (A.QuoteContext i) = return $ C.QuoteContext (getRange i)
    toConcrete (A.Quote i) = return $ C.Quote (getRange i)
    toConcrete (A.QuoteTerm i) = return $ C.QuoteTerm (getRange i)
    toConcrete (A.Unquote i) = return $ C.Unquote (getRange i)
    toConcrete (A.Tactic i e xs ys) = do
      e' <- toConcrete e
      xs' <- toConcrete xs
      ys' <- toConcrete ys
      let r      = getRange i
          rawtac = foldl (C.App r) e' xs'
      return $ C.Tactic (getRange i) rawtac (map namedArg ys')

    -- Andreas, 2012-04-02: TODO!  print DontCare as irrAxiom
    -- Andreas, 2010-10-05 print irrelevant things as ordinary things
    toConcrete (A.DontCare e) = C.Dot r . C.Paren r  <$> toConcrete e
       where r = getRange e
--    toConcrete (A.DontCare e) = C.DontCare <$> toConcreteTop e
{-
    -- Andreas, 2010-09-21 abuse C.Underscore to print irrelevant things
    toConcrete (A.DontCare) = return $ C.Underscore noRange Nothing
-}
    toConcrete (A.PatternSyn n) = C.Ident <$> toConcrete n

makeDomainFree :: A.LamBinding -> A.LamBinding
makeDomainFree b@(A.DomainFull (A.TypedBindings r (Common.Arg info (A.TBind _ [WithHiding h x] t)))) =
  case unScope t of
    A.Underscore MetaInfo{metaNumber = Nothing} -> A.DomainFree (mapHiding (mappend h) info) x
    _ -> b
makeDomainFree b = b

instance ToConcrete a c => ToConcrete (FieldAssignment' a) (FieldAssignment' c) where
    toConcrete = traverse toConcrete

-- Binder instances -------------------------------------------------------

instance ToConcrete A.LamBinding [C.LamBinding] where
    bindToConcrete (A.DomainFree info x) ret = do info <- toConcrete info
                                                  bindToConcrete x $ ret . (:[]) . C.DomainFree info . mkBoundName_
    bindToConcrete (A.DomainFull b)      ret = bindToConcrete b $ ret . map C.DomainFull

instance ToConcrete A.TypedBindings [C.TypedBindings] where
  bindToConcrete (A.TypedBindings r bs) ret =
    bindToConcrete bs $ \cbs ->
    ret (map (C.TypedBindings r) $ recoverLabels bs cbs)
    where
      recoverLabels :: A.Arg A.TypedBinding -> C.Arg C.TypedBinding -> [C.Arg C.TypedBinding]
      recoverLabels b cb
        | getHiding b == NotHidden = [cb]   -- We don't care about labels for explicit args
        | otherwise = traverse (recover (unArg b)) cb

      recover (A.TBind _ xs _) (C.TBind r ys e) = tbind r e (zipWith label xs ys)
      recover A.TLet{}         c@C.TLet{}       = [c]
      recover _ _ = __IMPOSSIBLE__

      tbinds r e [] = []
      tbinds r e xs = [ C.TBind r xs e ]

      tbind r e xs =
        case span ((\ x -> boundLabel x == boundName x) . dget) xs of
          (xs, x:ys) -> tbinds r e xs ++ [ C.TBind r [x] e ] ++ tbind r e ys
          (xs, [])   -> tbinds r e xs

      label x = fmap $ \ y -> y { boundLabel = nameConcrete $ dget x }

instance ToConcrete A.TypedBinding C.TypedBinding where
    bindToConcrete (A.TBind r xs e) ret =
        bindToConcrete xs $ \ xs -> do
        e <- toConcreteTop e
        ret $ C.TBind r (map (fmap mkBoundName_) xs) e
    bindToConcrete (A.TLet r lbs) ret =
        bindToConcrete lbs $ \ ds -> do
        ret $ C.TLet r $ concat ds

instance ToConcrete LetBinding [C.Declaration] where
    bindToConcrete (LetBind i info x t e) ret =
        bindToConcrete x $ \x ->
        do (t,(e, [], [], [])) <- toConcrete (t, A.RHS e)
           info <- toConcrete info
           ret [ C.TypeSig info x t
               , C.FunClause (C.LHS (C.IdentP $ C.QName x) [] [] [])
                             e C.NoWhere
               ]
    -- TODO: bind variables
    bindToConcrete (LetPatBind i p e) ret = do
        p <- toConcrete p
        e <- toConcrete e
        ret [ C.FunClause (C.LHS p [] [] []) (C.RHS e) NoWhere ]
    bindToConcrete (LetApply i x modapp _ _) ret = do
      x' <- unqualify <$> toConcrete x
      modapp <- toConcrete modapp
      let r = getRange modapp
          open = maybe DontOpen id $ minfoOpenShort i
          dir  = maybe defaultImportDir{ importDirRange = r } id $ minfoDirective i
      -- This is no use since toAbstract LetDefs is in localToAbstract.
      local (openModule' x dir id) $
        ret [ C.ModuleMacro (getRange i) x' modapp open dir ]
    bindToConcrete (LetOpen i x) ret = do
      x' <- toConcrete x
      let dir = maybe defaultImportDir id $ minfoDirective i
      local (openModule' x dir restrictPrivate) $
            ret [ C.Open (getRange i) x' dir ]

data AsWhereDecls = AsWhereDecls [A.Declaration]

instance ToConcrete AsWhereDecls WhereClause where
  bindToConcrete (AsWhereDecls []) ret = ret C.NoWhere
  bindToConcrete (AsWhereDecls ds@[Section _ am _ _]) ret = do
    ds' <- declsToConcrete ds
    cm  <- unqualify <$> lookupModule am
    let wh' = (if isNoName cm then AnyWhere else SomeWhere cm) $ ds'
    local (openModule' am defaultImportDir id) $ ret wh'
  bindToConcrete (AsWhereDecls ds) ret =
    ret . AnyWhere =<< declsToConcrete ds

mergeSigAndDef :: [C.Declaration] -> [C.Declaration]
mergeSigAndDef (C.RecordSig _ x bs e : C.Record r y ind eta c _ Nothing fs : ds)
  | x == y = C.Record r y ind eta c bs (Just e) fs : mergeSigAndDef ds
mergeSigAndDef (C.DataSig _ _ x bs e : C.Data r i y _ Nothing cs : ds)
  | x == y = C.Data r i y bs (Just e) cs : mergeSigAndDef ds
mergeSigAndDef (d : ds) = d : mergeSigAndDef ds
mergeSigAndDef [] = []

openModule' :: A.ModuleName -> ImportDirective -> (Scope -> Scope) -> Env -> Env
openModule' x dir restrict env = env{currentScope = sInfo{scopeModules = mods'}}
  where sInfo = currentScope env
        amod  = scopeCurrent sInfo
        mods  = scopeModules sInfo
        news  = setScopeAccess PrivateNS
                $ applyImportDirective dir
                $ maybe emptyScope restrict
                $ Map.lookup x mods
        mods' = Map.update (Just . (`mergeScope` news)) amod mods


-- Declaration instances --------------------------------------------------

declsToConcrete :: [A.Declaration] -> AbsToCon [C.Declaration]
declsToConcrete ds = mergeSigAndDef . concat <$> toConcrete ds

instance ToConcrete A.RHS (C.RHS, [C.Expr], [C.Expr], [C.Declaration]) where
    toConcrete (A.RHS e) = do
      e <- toConcrete e
      return (C.RHS e, [], [], [])
    toConcrete A.AbsurdRHS = return (C.AbsurdRHS, [], [], [])
    toConcrete (A.WithRHS _ es cs) = do
      es <- toConcrete es
      cs <- concat <$> toConcrete cs
      return (C.AbsurdRHS, [], es, cs)
    toConcrete (A.RewriteRHS xeqs rhs wh) = do
      wh <- declsToConcrete wh
      (rhs, eqs', es, whs) <- toConcrete rhs
      unless (null eqs')
        __IMPOSSIBLE__
      eqs <- toConcrete $ map snd xeqs
      return (rhs, eqs, es, wh ++ whs)

instance ToConcrete (Maybe A.QName) (Maybe C.Name) where
  toConcrete Nothing = return Nothing
  toConcrete (Just x) = do
    x' <- toConcrete (qnameName x)
    return $ Just x'

{- UNUSED
-- | Helper function used in instance @ToConcrete Definition@.
telToTypedBindingss :: [C.LamBinding] -> [C.TypedBindings]
telToTypedBindingss = map lamBindingToTypedBindings where

  lamBindingToTypedBindings :: C.LamBinding -> C.TypedBindings
  lamBindingToTypedBindings b =
    case b of
      C.DomainFull t     -> t
      C.DomainFree info n -> C.TypedBindings noRange $
        Common.Arg info $ C.TBind noRange [n] $ C.Underscore noRange Nothing
-}

instance ToConcrete (Constr A.Constructor) C.Declaration where
  toConcrete (Constr (A.ScopedDecl scope [d])) =
    withScope scope $ toConcrete (Constr d)
  toConcrete (Constr (A.Axiom _ i info x t)) = do
    x' <- unsafeQNameToName <$> toConcrete x
    t' <- toConcreteTop t
    info <- toConcrete info
    return $ C.TypeSig info x' t'
  toConcrete (Constr d) = head <$> toConcrete d

instance ToConcrete a C.LHS => ToConcrete (A.Clause' a) [C.Declaration] where
  toConcrete (A.Clause lhs rhs wh catchall) =
      bindToConcrete lhs $ \lhs ->
        case lhs of
          C.LHS p wps _ _ -> do
            bindToConcrete (AsWhereDecls wh)  $ \wh' -> do
                (rhs', eqs, with, wcs) <- toConcreteTop rhs
                return $ FunClause (C.LHS p wps eqs with) rhs' wh' : wcs
          C.Ellipsis {} -> __IMPOSSIBLE__
          -- TODO: Is the case above impossible? Previously there was
          -- no code for it, but GHC 7's completeness checker spotted
          -- that the case was not covered.

instance ToConcrete A.ModuleApplication C.ModuleApplication where
  toConcrete (A.SectionApp tel y es) = do
    y  <- toConcreteCtx FunctionCtx y
    bindToConcrete tel $ \tel -> do
      es <- toConcreteCtx ArgumentCtx es
      let r = fuseRange y es
      return $ C.SectionApp r (concat tel) (foldl (C.App r) (C.Ident y) es)

  toConcrete (A.RecordModuleIFS recm) = do
    recm <- toConcrete recm
    return $ C.RecordModuleIFS (getRange recm) recm

instance ToConcrete A.Declaration [C.Declaration] where
  toConcrete (ScopedDecl scope ds) =
    withScope scope (declsToConcrete ds)

  toConcrete (Axiom _ i info x t) = do
    x' <- unsafeQNameToName <$> toConcrete x
    withAbstractPrivate i $
      withInfixDecl i x'  $ do
      t' <- toConcreteTop t
      info <- toConcrete info
      return [C.Postulate (getRange i) [C.TypeSig info x' t']]

  toConcrete (A.Field i x t) = do
    x' <- unsafeQNameToName <$> toConcrete x
    withAbstractPrivate i $
      withInfixDecl i x'  $ do
      t' <- toConcreteTop t
      return [C.Field x' t']

  toConcrete (A.Primitive i x t) = do
    x' <- unsafeQNameToName <$> toConcrete x
    withAbstractPrivate i $
      withInfixDecl i x'  $ do
      t' <- toConcreteTop t
      return [C.Primitive (getRange i) [C.TypeSig defaultArgInfo x' t']]
        -- Primitives are always relevant.

  toConcrete (A.FunDef i _ _ cs) =
    withAbstractPrivate i $ concat <$> toConcrete cs

  toConcrete (A.DataSig i x bs t) =
    withAbstractPrivate i $
    bindToConcrete bs $ \tel' -> do
      x' <- unsafeQNameToName <$> toConcrete x
      t' <- toConcreteTop t
      return [ C.DataSig (getRange i) Inductive x' (map C.DomainFull $ concat tel') t' ]

  toConcrete (A.DataDef i x bs cs) =
    withAbstractPrivate i $
    bindToConcrete (map makeDomainFree bs) $ \tel' -> do
      (x',cs') <- (unsafeQNameToName -*- id) <$> toConcrete (x, map Constr cs)
      return [ C.Data (getRange i) Inductive x' (concat tel') Nothing cs' ]

  toConcrete (A.RecSig i x bs t) =
    withAbstractPrivate i $
    bindToConcrete bs $ \tel' -> do
      x' <- unsafeQNameToName <$> toConcrete x
      t' <- toConcreteTop t
      return [ C.RecordSig (getRange i) x' (map C.DomainFull $ concat tel') t' ]

  toConcrete (A.RecDef  i x ind eta c bs t cs) =
    withAbstractPrivate i $
    bindToConcrete (map makeDomainFree bs) $ \tel' -> do
      (x',cs') <- (unsafeQNameToName -*- id) <$> toConcrete (x, map Constr cs)
      return [ C.Record (getRange i) x' ind eta Nothing (concat tel') Nothing cs' ]

  toConcrete (A.Mutual i ds) = declsToConcrete ds

  toConcrete (A.Section i x tel ds) = do
    x <- toConcrete x
    bindToConcrete tel $ \tel -> do
      ds <- declsToConcrete ds
      return [ C.Module (getRange i) x (concat tel) ds ]

  toConcrete (A.Apply i x modapp _ _) = do
    x  <- unsafeQNameToName <$> toConcrete x
    modapp <- toConcrete modapp
    let r = getRange modapp
        open = fromMaybe DontOpen $ minfoOpenShort i
        dir  = fromMaybe defaultImportDir{ importDirRange = r } $ minfoDirective i
    return [ C.ModuleMacro (getRange i) x modapp open dir ]

  toConcrete (A.Import i x) = do
    x <- toConcrete x
    let open = maybe DontOpen id $ minfoOpenShort i
        dir  = maybe defaultImportDir id $ minfoDirective i
    return [ C.Import (getRange i) x Nothing open dir]

  toConcrete (A.Pragma i p)     = do
    p <- toConcrete $ RangeAndPragma (getRange i) p
    return [C.Pragma p]

  toConcrete (A.Open i x) = do
    x <- toConcrete x
    return [C.Open (getRange i) x defaultImportDir]

  toConcrete (A.PatternSynDef x xs p) = do
    C.QName x <- toConcrete x
    bindToConcrete xs $ \xs -> (:[]) . C.PatternSyn (getRange x) x xs <$> toConcrete p

  toConcrete (A.UnquoteDecl _ i x e) = do
    C.QName x <- toConcrete x
    (:[]) . C.UnquoteDecl (getRange i) x <$> toConcrete e

  toConcrete (A.UnquoteDef i x e) = do
    C.QName x <- toConcrete x
    (:[]) . C.UnquoteDef (getRange i) x <$> toConcrete e


data RangeAndPragma = RangeAndPragma Range A.Pragma

instance ToConcrete RangeAndPragma C.Pragma where
  toConcrete (RangeAndPragma r p) = case p of
    A.OptionsPragma xs  -> return $ C.OptionsPragma r xs
    A.BuiltinPragma b e      -> C.BuiltinPragma r b <$> toConcrete e
    A.BuiltinNoDefPragma b x -> C.BuiltinPragma r b . C.Ident <$>
      toConcrete x
    A.RewritePragma x        -> C.RewritePragma r <$> toConcrete x
    A.CompiledTypePragma x hs -> do
      x <- toConcrete x
      return $ C.CompiledTypePragma r x hs
    A.CompiledDataPragma x hs hcs -> do
      x <- toConcrete x
      return $ C.CompiledDataPragma r x hs hcs
    A.CompiledDeclareDataPragma x hs -> do
      x <- toConcrete x
      return $ C.CompiledDeclareDataPragma r x hs
    A.CompiledPragma x hs -> do
      x <- toConcrete x
      return $ C.CompiledPragma r x hs
    A.CompiledExportPragma x hs -> do
      x <- toConcrete x
      return $ C.CompiledExportPragma r x hs
    A.CompiledEpicPragma x e -> do
      x <- toConcrete x
      return $ C.CompiledEpicPragma r x e
    A.CompiledJSPragma x e -> do
      x <- toConcrete x
      return $ C.CompiledJSPragma r x e
    A.CompiledUHCPragma x cr -> do
      x <- toConcrete x
      return $ C.CompiledUHCPragma r x cr
    A.CompiledDataUHCPragma x crd crcs -> do
      x <- toConcrete x
      return $ C.CompiledDataUHCPragma r x crd crcs
    A.NoSmashingPragma x -> C.NoSmashingPragma r <$> toConcrete x
    A.StaticPragma x -> C.StaticPragma r <$> toConcrete x
    A.DisplayPragma f ps rhs ->
      C.DisplayPragma r <$> toConcrete (A.DefP (PatRange noRange) f ps) <*> toConcrete rhs

-- Left hand sides --------------------------------------------------------

noImplicitArgs :: A.Patterns -> A.Patterns
noImplicitArgs = filter (noImplicit . namedArg)

noImplicitPats :: [A.Pattern] -> [A.Pattern]
noImplicitPats = filter noImplicit

noImplicit :: A.Pattern -> Bool
noImplicit (A.WildP _) = False
noImplicit _           = True

instance ToConcrete A.SpineLHS C.LHS where
  bindToConcrete lhs = bindToConcrete (A.spineToLhs lhs :: A.LHS)

instance ToConcrete A.LHS C.LHS where
    bindToConcrete (A.LHS i lhscore wps) ret = do
      bindToConcreteCtx TopCtx lhscore $ \lhs ->
        bindToConcreteCtx TopCtx (noImplicitPats wps) $ \wps ->
          ret $ C.LHS lhs wps [] []

instance ToConcrete A.LHSCore C.Pattern where
    bindToConcrete = bindToConcrete . lhsCoreToPattern

appBrackets' :: [arg] -> Precedence -> Bool
appBrackets' []    _   = False
appBrackets' (_:_) ctx = appBrackets ctx

-- TODO: bind variables properly
instance ToConcrete A.Pattern C.Pattern where
    toConcrete (VarP x)    = toConcrete x >>= return . IdentP . C.QName
    toConcrete (A.WildP i)         =
        return $ C.WildP (getRange i)
    toConcrete (ConP i (AmbQ []) args) = __IMPOSSIBLE__
    toConcrete p@(ConP i (AmbQ (x:_)) args) =
      tryToRecoverOpAppP p $
        bracketP_ (appBrackets' args) $ do
            x <- toConcrete x
            args <- toConcreteCtx ArgumentCtx (noImplicitArgs args)
            return $ foldl AppP (C.IdentP x) args
    toConcrete p@(DefP i x args) =
      tryToRecoverOpAppP p $
        bracketP_ (appBrackets' args) $ do
            x <- toConcrete x
            args <- toConcreteCtx ArgumentCtx (noImplicitArgs args)
            return $ foldl AppP (C.IdentP x) args
    toConcrete (A.AsP i x p)   = do
      (x, p) <- toConcreteCtx ArgumentCtx (x,p)
      return $ C.AsP (getRange i) x p
    toConcrete (A.AbsurdP i) = return $ C.AbsurdP (getRange i)
    toConcrete (A.LitP (LitQName r x)) = do
      x <- lookupQName NoAmbiguousConstructors x
      bracketP_ appBrackets $ return $ AppP (C.QuoteP r) (defaultNamedArg (C.IdentP x))
    toConcrete (A.LitP l)    = return $ C.LitP l
    toConcrete (A.DotP i e)  = do
        e <- toConcreteCtx DotPatternCtx e
        return $ C.DotP (getRange i) e
    toConcrete (A.PatternSynP i n _) = IdentP <$> toConcrete n
    toConcrete (A.RecP i as) = C.RecP (getRange i) <$> mapM (traverse toConcrete) as

-- Helpers for recovering C.OpApp ------------------------------------------

data Hd = HdVar A.Name | HdCon A.QName | HdDef A.QName

cOpApp :: Range -> C.QName -> A.Name -> [C.Expr] -> C.Expr
cOpApp r x n es =
  C.OpApp r x (Set.singleton n)
          (map (defaultNamedArg . NoPlaceholder . Ordinary) es)

tryToRecoverOpApp :: A.Expr -> AbsToCon C.Expr -> AbsToCon C.Expr
tryToRecoverOpApp e def = recoverOpApp bracket cOpApp view e def
  where
    view e = do
      let Application hd args = AV.appView e
      case hd of
        Var x            -> Just (HdVar x, args)
        Def f            -> Just (HdDef f, args)
        Con (AmbQ (c:_)) -> Just (HdCon c, args)
        Con (AmbQ [])    -> __IMPOSSIBLE__
        _                -> Nothing

tryToRecoverOpAppP :: A.Pattern -> AbsToCon C.Pattern -> AbsToCon C.Pattern
tryToRecoverOpAppP p def = recoverOpApp bracketP_ opApp view p def
  where
    opApp r x n ps =
      C.OpAppP r x (Set.singleton n) (map defaultNamedArg ps)

    view p = case p of
      ConP _ (AmbQ (c:_)) ps -> Just (HdCon c, ps)
      DefP _ f            ps -> Just (HdDef f, ps)
      _                      -> Nothing

recoverOpApp :: (ToConcrete a c, HasRange c)
  => ((Precedence -> Bool) -> AbsToCon c -> AbsToCon c)
  -> (Range -> C.QName -> A.Name -> [c] -> c)
  -> (a -> Maybe (Hd, [A.NamedArg a]))
  -> a
  -> AbsToCon c
  -> AbsToCon c
recoverOpApp bracket opApp view e mDefault = case view e of
  Nothing -> mDefault
  Just (hd, args)
    | all notHidden args  -> do
      let  args' = map namedArg args
      case hd of
        HdVar  n
          | isNoName n    -> mDefault
          | otherwise     -> doQNameHelper id        C.QName  n args'
        HdDef qn          -> doQNameHelper qnameName id      qn args'
        HdCon qn          -> doQNameHelper qnameName id      qn args'
    | otherwise           -> mDefault
  where

  doQNameHelper fixityHelper conHelper n as = do
    x <- toConcrete n
    doQName (theFixity $ nameFixity n') (conHelper x) n' as
    where n' = fixityHelper n

  -- fall-back (wrong number of arguments or no holes)
  doQName _ x _ es
    | length xs == 1        = mDefault
    | length es /= numHoles = mDefault
    | null es               = mDefault
    where
      xs       = C.nameParts $ C.unqualify x
      numHoles = length (filter (== Hole) xs)

  -- binary case
  doQName fixity x n as
    | Hole <- head xs
    , Hole <- last xs = do
        let a1  = head as
            an  = last as
            as' = case as of
                    as@(_ : _ : _) -> init $ tail as
                    _              -> __IMPOSSIBLE__
        e1 <- toConcreteCtx (LeftOperandCtx fixity) a1
        es <- mapM (toConcreteCtx InsideOperandCtx) as'
        en <- toConcreteCtx (RightOperandCtx fixity) an
        bracket (opBrackets fixity)
          $ return $ opApp (getRange (e1, en)) x n ([e1] ++ es ++ [en])
    where
      xs = C.nameParts $ C.unqualify x

  -- prefix
  doQName fixity x n as
    | Hole <- last xs = do
        let an  = last as
            as' = case as of
                    as@(_ : _) -> init as
                    _          -> __IMPOSSIBLE__
        es <- mapM (toConcreteCtx InsideOperandCtx) as'
        en <- toConcreteCtx (RightOperandCtx fixity) an
        bracket (opBrackets fixity)
          $ return $ opApp (getRange (n, en)) x n (es ++ [en])
    where
      xs = C.nameParts $ C.unqualify x

  -- postfix
  doQName fixity x n as
    | Hole <- head xs = do
        let a1  = head as
            as' = tail as
        e1 <- toConcreteCtx (LeftOperandCtx fixity) a1
        es <- mapM (toConcreteCtx InsideOperandCtx) as'
        bracket (opBrackets fixity)
          $ return $ opApp (getRange (e1, n)) x n ([e1] ++ es)
    where
      xs = C.nameParts $ C.unqualify x

  -- roundfix
  doQName _ x n as = do
    es <- mapM (toConcreteCtx InsideOperandCtx) as
    bracket roundFixBrackets
      $ return $ opApp (getRange x) x n es

-- Some instances that are related to interaction with users -----------

instance ToConcrete InteractionId C.Expr where
    toConcrete (InteractionId i) = return $ C.QuestionMark noRange (Just i)

instance ToConcrete NamedMeta C.Expr where
    toConcrete i = do
      return $ C.Underscore noRange (Just $ prettyShow i)
