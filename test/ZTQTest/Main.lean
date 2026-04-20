import ZTQTest

/-!
# Test Runner

Main test runner that executes all test suites.
-/

def main : IO UInt32 := do
  IO.println "======================================"
  IO.println "     MyProject Test Suite"
  IO.println "======================================"
  IO.println ""

  try
    -- Run all test modules
    ZTQTest.Core.runTests
    ZTQTest.Utils.runTests

    IO.println "======================================"
    IO.println "    PASS: All tests passed!"
    IO.println "======================================"
    return 0
  catch e =>
    IO.println ""
    IO.println "======================================"
    IO.println "    FAIL: Test failure!"
    IO.println "======================================"
    IO.println s!"Error: {e}"
    return 1