module Curry.Files.CymakePath (getCymake,cymakeVersion) where

import Data.Version
import System.FilePath
import Paths_curry_frontend

cymakeVersion = showVersion version
getCymake     = do
  cymakeDir <- getBinDir
  return (cymakeDir </> "cymake")
