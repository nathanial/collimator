import Lake
open Lake DSL

package collimator where
  version := v!"0.1.0"
  -- Disable docPrime linter (warns about primed names like Lens')
  weakLeanArgs := #["-Dweak.linter.docPrime=false"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

require crucible from git "https://github.com/nathanial/crucible" @ "v0.0.3"

@[default_target]
lean_lib Collimator where
  roots := #[`Collimator]

-- Test library
lean_lib CollimatorTests where
  globs := #[.submodules `CollimatorTests]

-- Test runner executable
@[test_driver]
lean_exe collimator_tests where
  root := `CollimatorTests.Main
