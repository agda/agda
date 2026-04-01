{-# OPTIONS_GHC -Wunused-imports #-}
-- {-# OPTIONS_GHC -ddump-simpl -dsuppress-all -dno-suppress-type-signatures -ddump-to-file -dno-typeable-binds #-}

-- | Extract used definitions from terms.

module Agda.Syntax.Internal.Defs where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Utils.ExpandCase
import Agda.Utils.StrictEndo
import Agda.Utils.Impossible

-- | Get list of definitions, throw an error if any metavariable is encountered.
getDefListNoMetas :: Term -> [QName]
getDefListNoMetas a =
  getDefs (\_ -> __IMPOSSIBLE__) (\x -> Endo \xs -> x:xs) a `appEndo` []

-- | Getting the used definitions.
--
-- Note: in contrast to 'Agda.Syntax.Internal.Generic.foldTerm'
-- @getDefs@ also collects from sorts in terms.
-- Thus, this is not an instance of @foldTerm@.
class GetDefs a where

  -- | @getDefs lookup emb a@ extracts all used definitions
  --   (functions, data/record types) from @a@, embedded into a monoid via @emb@.
  --   Instantiations of meta variables are obtained via @lookup@.
  --
  --   Typical monoid instances would be @Endo [QName]@ or @Set QName@. Do not use @[QName]@
  --   because of obvious quadratic slowdown.
  --   Note that @emb@ can also choose to discard a used definition
  --   by mapping to the unit of the monoid.
  getDefs :: (Monoid m, ExpandCase m) => (MetaId -> Maybe Term) -> (QName -> m) -> a -> m

  -- {-# INLINE getDefs #-}
  -- default getDefs ::
  --      (Foldable f, GetDefs b, f b ~ a, Monoid m, ExpandCase m)
  --   => (MetaId -> Maybe Term) -> (QName -> m) -> a -> m
  -- getDefs ms ds = foldMap (getDefs ms ds)

instance GetDefs Clause where
  getDefs ms ds cl =
    expand \ret -> ret $ getDefs ms ds (clauseBody cl)

instance GetDefs Term where
  getDefs ms ds t = expand \ret -> case t of
    Def d vs   -> ret $ ds d <> getDefs ms ds vs
    Con _ _ vs -> ret $ getDefs ms ds vs
    Lit l      -> ret $ mempty
    Var i vs   -> ret $ getDefs ms ds vs
    Lam _ v    -> ret $ getDefs ms ds v
    Pi a b     -> ret $ getDefs ms ds a <> getDefs ms ds b
    Sort s     -> ret $ getDefs ms ds s
    Level l    -> ret $ getDefs ms ds l
    MetaV x vs -> ret $ getDefs ms ds x <> getDefs ms ds vs
    DontCare v -> ret $ getDefs ms ds v
    Dummy{}    -> ret $ mempty

instance GetDefs MetaId where
  getDefs ms ds x = getDefs ms ds (ms x)

instance GetDefs Type where
  getDefs ms ds a = expand \ret -> case a of
    El s t -> ret $ getDefs ms ds s <> getDefs ms ds t

instance GetDefs Sort where
  getDefs ms ds s = expand \ret -> case s of
    Univ _ l       -> ret $ getDefs ms ds l
    Inf _ _        -> ret $ mempty
    SizeUniv       -> ret $ mempty
    LockUniv       -> ret $ mempty
    LevelUniv      -> ret $ mempty
    IntervalUniv   -> ret $ mempty
    PiSort a s1 s2 -> ret $ getDefs ms ds a <> getDefs ms ds s1 <> getDefs ms ds s2
    FunSort s1 s2  -> ret $ getDefs ms ds s1 <> getDefs ms ds s2
    UnivSort s     -> ret $ getDefs ms ds s
    MetaS x es     -> ret $ getDefs ms ds x <> getDefs ms ds es
    DefS d es      -> ret $ ds d <> getDefs ms ds es
    DummyS{}       -> ret $ mempty

instance GetDefs Level where
  getDefs ms ds l = expand \ret -> case l of Max _ ls -> ret $ getDefs ms ds ls

instance GetDefs PlusLevel where
  getDefs ms ds l = expand \ret -> case l of Plus _ l -> ret $ getDefs ms ds l

-- collection instances
instance GetDefs a => GetDefs (Maybe a) where
  {-# INLINE getDefs #-}
  getDefs ms ds ma = expand \ret -> case ma of
    Nothing -> ret mempty
    Just a  -> ret $ getDefs ms ds a

instance GetDefs a => GetDefs [a] where
  {-# INLINE getDefs #-}
  getDefs ms ds = go where
    go as = expand \ret -> case as of
      []   -> ret mempty
      a:as -> ret $ getDefs ms ds a <> go as

instance GetDefs a => GetDefs (Elim' a) where
  {-# INLINE getDefs #-}
  getDefs ms ds e = expand \ret -> case e of
    Apply t      -> ret $ getDefs ms ds t
    Proj _ _     -> ret $ mempty
    IApply l r t -> ret $ getDefs ms ds l <> getDefs ms ds r <> getDefs ms ds t

instance GetDefs a => GetDefs (Arg a) where
  {-# INLINE getDefs #-}
  getDefs ms ds a = expand \ret -> case a of
    Arg _ t -> ret $ getDefs ms ds t

instance GetDefs a => GetDefs (Dom a) where
  {-# INLINE getDefs #-}
  getDefs ms ds d = expand \ret -> case d of
    Dom _ _ _ _ t -> ret $ getDefs ms ds t

instance GetDefs a => GetDefs (Abs a) where
  {-# INLINE getDefs #-}
  getDefs ms ds a = expand \ret -> case a of
    Abs _ t   -> ret $ getDefs ms ds t
    NoAbs _ t -> ret $ getDefs ms ds t

instance (GetDefs a, GetDefs b) => GetDefs (a,b) where
  {-# INLINE getDefs #-}
  getDefs ms ds ab = expand \ret -> case ab of (a,b) -> ret $ getDefs ms ds a <> getDefs ms ds b

instance GetDefs Telescope where
  getDefs ms ds = getDefs ms ds . telToList

-- no defs here
instance {-# OVERLAPPING #-} GetDefs String where
  getDefs _ _ _ = mempty
