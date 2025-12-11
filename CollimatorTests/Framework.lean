-- Re-export everything from submodules
import CollimatorTests.Framework.Core
import CollimatorTests.Framework.Macros
import CollimatorTests.Framework.SuiteRegistry

/-!
# Test Framework for Collimator

Simple test harness providing TestCase structure and assertion functions.

## New Syntax (Recommended)

```lean
import CollimatorTests.Framework

namespace CollimatorTests.MyTests

open CollimatorTests

testSuite "My Test Suite"

test "description of test" := do
  actualValue ≡ expectedValue
  optionValue ≡? expectedInner

#generate_tests

end CollimatorTests.MyTests
```

## Legacy Syntax (Still Supported)

```lean
private def case_foo : TestCase := {
  name := "Foo test",
  run := do ...
}

def cases : List TestCase := [case_foo, ...]
```
-/
