/-!
# IO, Exceptions, and Concurrency
-/

namespace ZeroToQED.Effects

-- ANCHOR: io_basics
def greet : IO Unit := do
  IO.println "What is your name?"
  let stdin ← IO.getStdin
  let name ← stdin.getLine
  IO.println s!"Hello, {name.trim}!"

def printNumbers : IO Unit := do
  for i in [1, 2, 3, 4, 5] do
    IO.println s!"Number: {i}"

def getCurrentTime : IO Unit := do
  let now ← IO.monoMsNow
  IO.println s!"Milliseconds since start: {now}"
-- ANCHOR_END: io_basics

-- ANCHOR: io_pure
def pureComputation : IO Nat := do
  let x := 10
  let y := 20
  return x + y

#eval pureComputation  -- 30

def combineIO : IO String := do
  let a ← pure "Hello"
  let b ← pure "World"
  return s!"{a} {b}"

#eval combineIO  -- "Hello World"
-- ANCHOR_END: io_pure

-- ANCHOR: file_io
def writeToFile (path : String) (content : String) : IO Unit := do
  IO.FS.writeFile path content

def readFromFile (path : String) : IO String := do
  IO.FS.readFile path

def appendToFile (path : String) (content : String) : IO Unit := do
  let handle ← IO.FS.Handle.mk path .append
  handle.putStrLn content

def copyFile (src dst : String) : IO Unit := do
  let content ← IO.FS.readFile src
  IO.FS.writeFile dst content
-- ANCHOR_END: file_io

-- ANCHOR: file_lines
def processLines (path : String) : IO (List String) := do
  let content ← IO.FS.readFile path
  return content.splitOn "\n"

def countLines (path : String) : IO Nat := do
  let lines ← processLines path
  return lines.length

def filterLines' (path : String) (pred : String → Bool) : IO (List String) := do
  let lines ← processLines path
  return lines.filter pred
-- ANCHOR_END: file_lines

-- ANCHOR: error_handling
def safeDivideIO (x y : Nat) : IO Nat := do
  if y == 0 then
    throw <| IO.userError "Division by zero"
  return x / y

def trySafeDivide : IO Unit := do
  try
    let result ← safeDivideIO 10 0
    IO.println s!"Result: {result}"
  catch e =>
    IO.println s!"Error: {e}"

def withDefault' {α : Type} (action : IO α) (default : α) : IO α := do
  try
    action
  catch _ =>
    return default
-- ANCHOR_END: error_handling

-- ANCHOR: io_ref
def counterExample : IO Nat := do
  let counter ← IO.mkRef 0
  for _ in List.range 10 do
    counter.modify (· + 1)
  counter.get

#eval counterExample  -- 10

def accumulate (values : List Nat) : IO Nat := do
  let sum ← IO.mkRef 0
  for v in values do
    sum.modify (· + v)
  sum.get

#eval accumulate [1, 2, 3, 4, 5]  -- 15
-- ANCHOR_END: io_ref

-- ANCHOR: except_t
abbrev AppM := ExceptT String IO

def validatePositive (n : Int) : AppM Int := do
  if n <= 0 then throw "Must be positive"
  return n

def validateRange (n : Int) (lo hi : Int) : AppM Int := do
  if n < lo || n > hi then throw s!"Must be between {lo} and {hi}"
  return n

def processNumber : AppM Int := do
  let n ← validatePositive 42
  let m ← validateRange n 0 100
  return m * 2

def runApp : IO Unit := do
  match ← processNumber.run with
  | .ok result => IO.println s!"Success: {result}"
  | .error msg => IO.println s!"Failed: {msg}"
-- ANCHOR_END: except_t

-- ANCHOR: reader_t
structure Config where
  verbose : Bool
  maxRetries : Nat
  timeout : Nat
  deriving Repr

abbrev ConfigM := ReaderT Config IO

def getVerbose : ConfigM Bool := do
  let cfg ← read
  return cfg.verbose

def logIfVerbose (msg : String) : ConfigM Unit := do
  if ← getVerbose then
    IO.println s!"[LOG] {msg}"

def runWithConfig : IO Unit := do
  let config : Config := { verbose := true, maxRetries := 3, timeout := 5000 }
  (logIfVerbose "Starting process").run config
-- ANCHOR_END: reader_t

-- ANCHOR: tasks_basic
def slowComputation (n : Nat) : IO Nat := do
  IO.sleep 100
  return n * 2

def runParallel : IO Unit := do
  let task1 ← IO.asTask (slowComputation 10)
  let task2 ← IO.asTask (slowComputation 20)
  let result1 ← IO.wait task1
  let result2 ← IO.wait task2
  match result1, result2 with
  | .ok r1, .ok r2 => IO.println s!"Results: {r1}, {r2}"
  | _, _ => IO.println "Task failed"
-- ANCHOR_END: tasks_basic

-- ANCHOR: tasks_map
def runBothTasks : IO (Nat × Nat) := do
  let task1 ← IO.asTask (slowComputation 10)
  let task2 ← IO.asTask (slowComputation 20)
  let r1 ← IO.wait task1
  let r2 ← IO.wait task2
  match r1, r2 with
  | .ok a, .ok b => return (a, b)
  | _, _ => throw <| IO.userError "Task failed"
-- ANCHOR_END: tasks_map

-- ANCHOR: process_io
def runCommand (cmd : String) (args : List String) : IO String := do
  let output ← IO.Process.output {
    cmd := cmd
    args := args.toArray
  }
  return output.stdout

def shellExample : IO Unit := do
  let result ← runCommand "echo" ["Hello", "World"]
  IO.println result
-- ANCHOR_END: process_io

-- ANCHOR: environment
def getEnvVar (name : String) : IO (Option String) := do
  IO.getEnv name

def printPath : IO Unit := do
  match ← getEnvVar "PATH" with
  | some path => IO.println s!"PATH: {path}"
  | none => IO.println "PATH not set"

def getCwd' : IO System.FilePath := do
  IO.currentDir
-- ANCHOR_END: environment

end ZeroToQED.Effects
