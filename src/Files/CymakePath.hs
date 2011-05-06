module Files.CymakePath (getCymake, cymakeGreeting, cymakeVersion) where

import Data.Version (showVersion)
import System.FilePath ((</>))
import Paths_curry_frontend

-- | Show a greeting of the current cymake
cymakeGreeting :: String
cymakeGreeting = "This is cymake, version " ++ cymakeVersion

-- | Retrieve the version number of cymake
cymakeVersion :: String
cymakeVersion = showVersion version

-- | Retrieve the location of the cymake executable
getCymake :: IO String
getCymake = do
  cymakeDir <- getBinDir
  return (cymakeDir </> "cymake")
