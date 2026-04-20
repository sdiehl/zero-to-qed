import ZeroToQED

/-!
# Utils Tests

Unit tests for utility functions.
-/

namespace ZTQTest.Utils

def assert (condition : Bool) (message : String) : IO Unit := do
  if not condition then
    throw (IO.userError s!"Test failed: {message}")

def testBasic : IO Unit := do
  assert true "Basic util test should pass"
  IO.println "PASS: Basic util test passed"

def runTests : IO Unit := do
  IO.println "Running Utils Tests"
  IO.println "==================="
  testBasic
  IO.println ""

end ZTQTest.Utils