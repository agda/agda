{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE NamedFieldPuns            #-}

import Data.Foldable
import Data.List ( intercalate )
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.ByteString.Char8 as BS

import System.Environment ( getArgs, getEnv )
import System.Exit ( exitFailure )
import System.IO ( hPutStrLn, stderr )

import GitHub.Auth ( Auth( OAuth ) )
-- import GitHub.Data.Id ( Id(..) )
import GitHub.Data.Issues ( Issue( Issue, issueMilestone, issueNumber, issueTitle, issueClosedBy, issueUrl ) )
import GitHub.Data.Name ( Name( N ) )
import GitHub.Data.Milestone ( Milestone( milestoneNumber, milestoneTitle ) )
import GitHub.Data.Options ( stateClosed )
import GitHub.Data.Options ( IssueState(..), IssueRepoMod(..) ) -- not exported:, FilterBy(..) )
import GitHub.Data.URL ( URL, getUrl )

import qualified GitHub.Endpoints.Issues.Milestones as GH ( milestones' )
import qualified GitHub.Endpoints.Issues as GH ( issuesForRepo' )

envGHToken = "GITHUBTOKEN"
owner = "agda"
repo  = "agda"
theRepo = owner ++ "/" ++ repo

main :: IO ()
main = getArgs >>= \case { [arg] -> run (Text.pack arg) ; _ -> usage }

usage :: IO ()
usage = putStrLn $ unlines
  [ "Usage: ClosedIssuesForMilestone <milestone>"
  , ""
  , "Retrieves closed issues for the given milestone from github repository"
  , theRepo ++ " and prints them as csv to stdout."
  ]

-- | Retrieve closed issues for the given milestone and print as csv to stdout.
run :: Text -> IO ()
run mileStoneTitle = do

  -- Get authentication token from environment.
  auth <- OAuth . BS.pack <$> getEnv envGHToken

  -- Log in to repo.

  -- Resolve milestone into milestone id.
  mileStoneVector <- crashOr $ GH.milestones' (Just auth) (N owner) (N repo)
  mileStoneId <- case filter ((mileStoneTitle ==) . milestoneTitle) $ toList mileStoneVector of
    []  -> die $ "Milestone " ++ Text.unpack mileStoneTitle ++ " not found in github repo " ++ theRepo
    [m] -> return $ milestoneNumber m
    ms  -> die $ "Milestone " ++ Text.unpack mileStoneTitle ++ " ambiguous in github repo " ++ theRepo

  -- Debug.
  -- print mileStoneId

  -- Get list of issues.
  issueVector <- crashOr $ GH.issuesForRepo' (Just auth) (N owner) (N repo) $ stateClosed
    -- Symbols not exported.
    -- IssueRepoMod $ \ o ->
    --   o { issueRepoOptionsMilestone = FilterBy mileStoneId
    --     , issueRepoOptionsState     = Just StateClosed
    --     }

  -- Filter by milestone.
  let issues = reverse
        [ i
        | i <- toList issueVector
        , m <- maybeToList $ issueMilestone i
        ,  milestoneNumber m == mileStoneId
        ]

  -- Print issues.

  forM_ issues $ \ Issue{ issueNumber, issueTitle } -> putStrLn $
    "  [#" ++ show issueNumber
    ++ "](https://github.com/" ++ theRepo ++ "/issues/" ++ show issueNumber
    ++ "): " ++ Text.unpack issueTitle

  -- TODO: output tsv
  --
  -- forM_ issues $ \ Issue{ issueNumber, issueTitle } -> do
  --   putStrLn $ intercalate "\t" $
  --     [ show issueNumber
  --     , Text.unpack issueTitle
  --     ]


-- | Crash on exception.
crashOr :: Show e => IO (Either e a) -> IO a
crashOr m = either (die . show) return =<< m

-- | Crash with error message
die :: String -> IO a
die e = do hPutStrLn stderr e; exitFailure
