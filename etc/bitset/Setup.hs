import Distribution.Simple
-- import System.FilePath
-- import Distribution.PackageDescription
-- import Distribution.Simple.LocalBuildInfo
-- import System

main = defaultMain


-- main = defaultMainWithHooks hooks
--   where hooks = simpleUserHooks { runTests = runTests' }

-- runTests' :: Args -> Bool -> PackageDescription -> LocalBuildInfo -> IO ()
-- runTests' _ _ _ lbi = system testprog >> return ()
--   where testprog = (buildDir lbi) </> "tests" </> "test"
