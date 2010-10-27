module Monads(module Monads, module Control.Monad) where

import AgdaTrace
import Error
import Position
--import IO
import Control.Monad

infix 0 `handle`
infix 0 `handle_`

--noInfo :: Position -> EMsg
--noInfo p = eMsg p (ETEMP "No information on this error")

class Monad m => ErrorMonad m where
 raise   :: EMsg                  -> m a
 handle  :: m a  -> (EMsg -> m a) -> m a
 handle_ :: m a  ->          m a  -> m a
 handle_ a b =  a `handle` (\_ -> b)

data Error a = Done !a | Err EMsg

instance Functor Error where
  fmap f (Done a ) = Done (f a)
  fmap f (Err msg) = Err  msg

instance Monad Error where
  return        = Done
  Done a  >>= f = f a
  Err msg >>= f = Err msg


instance ErrorMonad Error where
 raise              = Err
 Err msg `handle` f = f msg
 a       `handle` _ = a

newtype StateM s a = STM{funSTM:: s -> Error(a,s)} -- 'run' taken..

instance  Monad (StateM s) where
  return a    = STM$ \s-> Done (a,s)
  STM g >>= f = STM$ \s-> do (a,s')<- g s; funSTM (f a) s'

instance Functor (StateM s) where -- lookina at .hi and dump-stg ...
  -- fmap f (STM g) = STM$ fmap (\(a,s')->(f a, s')) . g
  fmap f (STM g) = STM(\s-> case g s of Done(a,s')-> Done(f a, s')
                                        Err  msg  -> Err msg)

instance ErrorMonad (StateM s) where
 raise msg  = STM$ \_ -> raise msg
 STM g `handle` f = STM$ \s -> g s `handle` (\msg -> funSTM (f msg) s)

-- Needs to be uncommented to compile with hbc
done :: Monad m => m ()
done = return ()

accessSTM f = STM f

readSTME :: (s -> Error a) -> StateM s a
readSTME f = STM$ \ s -> do x <- f s; return (x,s)

readSTM :: (s -> a) -> StateM s a
readSTM f = readSTME (return.f)

-- Should it be update :: (s -> s) -> StateM s s??

updateSTM :: (s -> s) -> StateM s ()
updateSTM f = STM$ \s -> Done((),f s)

updateSTMR :: (s -> (a,s)) -> StateM s a
updateSTMR f = STM$ Done . f

updateSTME :: (s -> Error s) -> StateM s ()
updateSTME f = STM$ \s -> do s' <- f s; return ((),s')

runSTM ::  StateM s a -> s -> Error a
runSTM (STM f) s = do (x,_) <- f s; return x

liftESTM :: Error a -> StateM s a
liftESTM (Done a) = return a
liftESTM (Err msg) = raise msg

traceM :: Monad m => String -> m ()
traceM s = trace (s++"\n") (return ())

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM mb m m' = do b <- mb; if b then m else m'

guardE :: ErrorMonad m => m Bool -> EMsg -> m ()
guardE mb msg = do b <- mb; if b then return () else raise msg


internalError :: ErrorMonad m => String -> m a
internalError msg = raise (noPosition,EInternal msg)

passError :: ErrorMonad m => PassMsg -> m a
passError msg = raise (noPosition,EPass msg)

liftEither :: ErrorMonad m => Either EMsg a -> m a
liftEither e = either raise return e

liftMaybeE :: Maybe a -> EMsg -> Error a
liftMaybeE ma er = maybe (raise er) Done ma

liftMaybeSTM :: Maybe a -> EMsg -> StateM s a
liftMaybeSTM m err = liftESTM (liftMaybeE m err)

mkMaybeError :: ErrorMonad m => m a -> m (Maybe a)
mkMaybeError m = Just `liftM` m `handle_` return Nothing

tempM :: StateM s a -> StateM s a
tempM (STM g) = STM$ \s -> case g s of Err  msg -> Err msg
                                       Done(a,_)-> Done$!(a,s)

{- -------------------------- -}
-- reader-state-error
data Error2 s a = Done2 !s !a | Err2 EMsg
elimError2 f g e = case e of Done2 s a-> f s a; Err2 msg-> g msg
instance Functor (Error2 s) where
  fmap f m = case m of Done2 s a-> Done2 s (f a); Err2 msg-> Err2 msg
newtype RSE r s a = RSE{runRSE::r-> s-> Error2 s a}
instance Functor (RSE r s) where
  -- fmap f (RSE g) = RSE$ \r s-> fmap f (g r s)
  fmap f (RSE g) = RSE(\r s-> case g r s of Done2 s' a-> Done2 s' (f a)
                                            Err2  msg -> Err2 msg)
instance Monad   (RSE r s) where
  return a      = RSE$ \_ s-> Done2 s a
  (RSE g) >>= f = RSE$ \r s-> case g r s of Done2 s' a-> runRSE (f a) r s'
                                            Err2  msg -> Err2 msg
instance ErrorMonad (RSE r s) where
  raise msg = RSE$ \_ _-> Err2 msg
  handle (RSE g) f = RSE$ \r s-> case g r s of Err2 msg-> runRSE (f msg) r s
                                               done    -> done
modifRSE f   = RSE$ \r s-> case f r s of (a,s')-> Done2 s' a
asksRSE  f   = RSE$ \r s-> Done2  s (f r)
askRSE       = asksRSE id
localRSE f m = RSE$ \r s-> runRSE m (f r) s
