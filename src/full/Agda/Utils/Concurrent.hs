-- | Utilities for concurrency.

module Agda.Utils.Concurrent where

-- standard base imports

import Control.Monad
import Control.Monad.IO.Class
import Data.Functor  ( (<&>) )
import Data.Hashable ( Hashable )
import Data.HashSet  ( HashSet)
import Data.Set      ( Set )
import qualified Data.HashSet as HashSet
import qualified Data.Set as Set

-- imports for concurrency

import Control.Concurrent
import Control.Concurrent.Async
import Control.Concurrent.STM
import Control.Concurrent.STM.TQueue (TQueue, newTQueueIO, tryReadTQueue, writeTQueue)

-- | Run simple IO tasks whose results can be collected in a monoid @b@.
--   The task description @a@ also serves as unique task id.
--
class (Eq a, Hashable a, Monoid b) => SimpleIOTask a b -- -- | a -> b
  where

  -- | Run an IO task returning new tasks and a result.
  runSimpleIOTask :: a -> IO ([a], b)

-- | The scheduler data of waiting, running and completed tasks
--   plus the cell to collect the results.
--
data SimpleIOScheduler a b = SimpleIOScheduler
  { waitingTasks     :: TQueue a
  , runningTasks     :: TVar (HashSet a)
  , completedTasks   :: TVar (HashSet a)
  , collectedResults :: TVar b
  }

-- |
data TaskAvailability a
  = TaskReserved a
  | PleaseRetry
  | NoTaskAvailable
  | AllTasksFinished

-- | Concurrently work a task list to completion
--   with the given number of workers.
--
runSimpleIOTasksConcurrently ::
     SimpleIOTask a b    -- ^ Task implementation.
  => Int                 -- ^ Number of concurrent workers
  -> [a]                 -- ^ Initial task list.
  -> IO b                -- ^ Final accumulated result after all tasks finished.
runSimpleIOTasksConcurrently n tasks = do
  -- Allocate the scheduler state
  st <- newSimpleIOScheduler tasks

  -- Create and fork multiple worker threads, wait for them to finish.
  replicateConcurrently_ n $ simpleIOWorker st

  -- Return final result
  readTVarIO $ collectedResults st

-- | Create scheduler data with an initial task list.
--
newSimpleIOScheduler :: (Eq a, Hashable a, Monoid b) => [a] -> IO (SimpleIOScheduler a b)
newSimpleIOScheduler tasks = SimpleIOScheduler
  <$> initTQueueIO tasks
  <*> newTVarIO HashSet.empty
  <*> newTVarIO HashSet.empty
  <*> newTVarIO mempty
  where
    initTQueueIO xs = do
      q <- newTQueueIO
      atomically $ mapM_ (writeTQueue q) xs
      return q

-- | Self-scheduling worker.
--
simpleIOWorker ::
     SimpleIOTask a b       -- ^ Task implementation.
  => SimpleIOScheduler a b  -- ^ Scheduler state.
  -> IO ()
simpleIOWorker st = do

  -- Check for an available task and reserve it, if any.
  grabSimpleIOTask st >>= \case

    AllTasksFinished -> return ()

    -- TODO: waiting for a fixed time is clumsy, need a queue for waiting workers
    -- or spawn workers freshly after each task.
    NoTaskAvailable  -> do
      threadDelay 1000 -- microseconds
      next

    PleaseRetry -> next

    TaskReserved task -> do

      -- Run the job.
      (tasks, res) <- runSimpleIOTask task

      -- Append the result.
      atomically $ modifyTVar' (collectedResults st) (<> res)

      -- Register the not already completed new tasks.
      completed <- atomically $ readTVar $ completedTasks st
      let new = filter (not . (`HashSet.member` completed)) tasks
      atomically $ mapM_ (writeTQueue $ waitingTasks st) new

      -- Report this task as no longer running.
      atomically $ modifyTVar' (runningTasks st) $ HashSet.delete task

      -- Continue working.
      next

  where
    next = simpleIOWorker st

-- | Check for an available task and reserve it, if any.
--
grabSimpleIOTask ::
     SimpleIOTask a b       -- ^ Task implementation.
  => SimpleIOScheduler a b  -- ^ Scheduler state.
  -> IO (TaskAvailability a)
grabSimpleIOTask st = do

  -- We have to move a task from waiting to running atomically.
  atomically $ do
    tryReadTQueue (waitingTasks st) >>= \case

      -- Task queue empty?
      Nothing -> do

        -- If no tasks are running then all tasks are finished.
        (null <$> readTVar (runningTasks st)) <&> \case
          True  -> AllTasksFinished
          False -> NoTaskAvailable

      -- Task queue nonempty: reserve task and mark it as "completed" and running.
      Just task -> do
        completed <- readTVar $ completedTasks st
        if task `HashSet.member` completed then return PleaseRetry else do
          modifyTVar (completedTasks st) (HashSet.insert task)
          modifyTVar (runningTasks   st) (HashSet.insert task)
          return $ TaskReserved task
