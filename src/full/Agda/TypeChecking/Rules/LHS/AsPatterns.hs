{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.LHS.AsPatterns
  ( recoverAsPatterns ) where

import Control.Applicative
import Control.Monad.Writer hiding ((<>))
import qualified Data.Foldable as Fold

import Agda.Syntax.Common
import Agda.Syntax.Concrete ()
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Abstract.Pattern ( containsAsPattern )
import qualified Agda.Syntax.Abstract as A

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Rules.LHS.Problem
import Agda.TypeChecking.Rules.LHS.Implicit
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Records
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce

import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.Size
import Agda.Utils.Impossible
#include "undefined.h"

recoverAsPatterns :: Telescope -> Type -> Term -> [NamedArg A.Pattern] -> [NamedArg DeBruijnPattern] -> TCM [AsBinding]
recoverAsPatterns delta a self ps qs = do
  let es = patternsToElims qs
  as <- typeElims (raise (size delta) a) self es
  ps <- insertImplicitPatternsT DontExpandLast ps a
  reportSDoc "tc.lhs.as" 30 $ vcat
    [ text "recovering as patterns"
    , nest 2 $ vcat [ text "es =" <+> prettyList (map prettyTCM es)
                    , text "as =" <+> prettyList (map prettyTCM as)
                    , text "ps =" <+> prettyList (map prettyA ps) ]
    ]
  execWriterT $ asPatterns as ps es

asPatterns :: [ElimType] -> [NamedArg A.Pattern] -> [Elim] -> WriterT [AsBinding] TCM ()
asPatterns _ [] _ = return ()
asPatterns (ProjT _ a : as) (p : ps) (Proj{} : vs) = do
  unless (isJust $ A.maybePostfixProjP p) __IMPOSSIBLE__  -- sanity check
  ps <- lift $ insertImplicitPatternsT DontExpandLast ps a
  asPatterns as ps vs
asPatterns (ArgT dom : as) (p : ps) (Apply v : vs)
  | not $ containsAsPattern p = asPatterns as ps vs
  | otherwise = do
    let a = unDom dom
    case namedArg p of
      A.AsP _ x p' -> do
        tell [AsB x (unArg v) a]
        asPatterns (ArgT dom : as) (fmap (p' <$) p : ps) (Apply v : vs)
      A.ConP _ _ ps' -> do
        (_, _, tel, as', args) <- lift $ conPattern a (unArg v)
        ps' <- lift $ insertImplicitPatterns ExpandLast ps' tel
        asPatterns (map ArgT as' ++ as) (ps' ++ ps) (map Apply args ++ vs)
      A.RecP i fps -> do
        (r, c, _, as', args) <- lift $ conPattern a (unArg v)
        let fs  = zipWith (<$) (map (nameConcrete . qnameName) $ conFields c) args
        ps' <- lift $ insertMissingFields r (const $ A.WildP i) fps fs
        asPatterns (map ArgT as' ++ as) (ps' ++ ps) (map Apply args ++ vs)
      A.DefP{} -> __IMPOSSIBLE__ -- ?
      _ -> __IMPOSSIBLE__
asPatterns _ _ _ = __IMPOSSIBLE__

-- | Given a fully applied constructor term and its type,
--   deconstruct it and return, amongst others, the types of its arguments.
conPattern
  :: Type  -- ^ Type need not be reduced.
  -> Term  -- ^ Fully applied constructor.
  -> TCM (QName, ConHead, Telescope, [Dom Type], Args)
       -- ^ Data/record type name,
       --   constructor name,
       --   argument telescope,
       --   types of arguments.
       --   arguments.
conPattern a (Con c ci args) = do
  -- @getFullyAppliedConType@ works since @c@ is fully applied.
  ((d, _, _), ca) <- fromMaybe __IMPOSSIBLE__ <.> getFullyAppliedConType c =<< reduce a
  TelV tel _ <- telView ca
  let as = fromMaybe __IMPOSSIBLE__ $ typeArgsWithTel tel $ map unArg args
  return (d, c, tel, as, args)
conPattern _ _ = __IMPOSSIBLE__
