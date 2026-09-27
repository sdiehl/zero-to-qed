import ZeroToQED

/-!
# Core Tests

Unit tests for core functionality.
-/

namespace ZTQTest.Core

-- Test helper to run assertions
def check (condition : Bool) (message : String) : IO Unit := do
  if not condition then
    throw (IO.userError s!"Test failed: {message}")

def testBasic : IO Unit := do
  check true "Basic test should pass"
  IO.println "PASS: Basic test passed"

def runTests : IO Unit := do
  IO.println "Running Core Tests"
  IO.println "=================="
  testBasic
  IO.println ""

end ZTQTest.Core
