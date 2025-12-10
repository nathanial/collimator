import Lake
open Lake DSL

package collimator where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

@[default_target]
lean_lib Collimator where
  globs := #[.submodules `Collimator]

-- Test library
lean_lib CollimatorTests where
  globs := #[.submodules `CollimatorTests]

-- Test runner executable
lean_exe collimator_tests where
  root := `CollimatorTests.Main
