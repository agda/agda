
-- -- -----------------------------------------------------------------------------
-- -- Exposing, Hiding, Unregistering are all similar

-- exposePackage :: PackageIdentifier -> Verbosity -> [Flag] -> Force -> IO ()
-- exposePackage = modifyPackage (\p -> [p{exposed=True}])

-- hidePackage :: PackageIdentifier -> Verbosity -> [Flag] -> Force -> IO ()
-- hidePackage = modifyPackage (\p -> [p{exposed=False}])

-- unregisterPackage :: PackageIdentifier -> Verbosity -> [Flag] -> Force -> IO ()
-- unregisterPackage = modifyPackage (\_ -> [])
