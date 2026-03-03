import Lean
import LeanAideCore.Config
open Lean Meta

instance : LeanAideBaseDir where
  baseDir := baseDirImpl

-- #eval getBaseDir
-- #eval resourcesDir
