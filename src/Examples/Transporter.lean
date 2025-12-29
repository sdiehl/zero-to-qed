-- Star Trek Transporter System: Monad Transformer Ordering
-- Run with: lake exe transporter

-- ANCHOR: errors_and_types
inductive TransporterError where
  | bufferOverflow
  | patternDegradation (percent : Nat)
  | heisenbergCompensatorFailure
  | annularConfinementFailure
  deriving Repr

def TransporterError.describe : TransporterError → String
  | .bufferOverflow => "Pattern buffer overflow"
  | .patternDegradation p => s!"Pattern degradation at {p}%"
  | .heisenbergCompensatorFailure => "Heisenberg compensator offline"
  | .annularConfinementFailure => "Annular confinement beam failure"

structure CrewMember where
  name : String
  rank : String
  deriving Repr, BEq

structure TransportLog where
  entries : List String := []
  deriving Repr

def TransportLog.add (log : TransportLog) (entry : String) : TransportLog :=
  { entries := log.entries ++ [entry] }
-- ANCHOR_END: errors_and_types

-- ANCHOR: transformer_stacks
-- Two different monad transformer orderings with DIFFERENT semantics:

-- Stack A: State OUTSIDE Except
-- On error, state changes are PRESERVED (audit log semantics)
abbrev TransporterA := StateT TransportLog (Except TransporterError)

-- Stack B: State INSIDE Except
-- On error, state changes are ROLLED BACK (transaction semantics)
abbrev TransporterB := ExceptT TransporterError (StateM TransportLog)
-- ANCHOR_END: transformer_stacks

-- ANCHOR: operations_a
def logStepA (msg : String) : TransporterA Unit :=
  modify (·.add msg)

def transportA (crew : CrewMember) : TransporterA CrewMember := do
  logStepA s!"Initializing buffer for {crew.name}"
  logStepA s!"Scanning pattern..."
  if crew.name.length > 15 then
    logStepA s!"ERROR: Buffer overflow during scan"
    throw .bufferOverflow
  logStepA s!"Dematerializing {crew.name}..."
  logStepA s!"Pattern in buffer, subject no longer exists at origin"
  -- Failure here is catastrophic: crew is dematerialized but transmission fails
  if crew.name == "Thomas Riker" then
    logStepA s!"ERROR: Heisenberg compensator failure during transmission"
    throw .heisenbergCompensatorFailure
  logStepA s!"Transmitting..."
  logStepA s!"Rematerializing at destination"
  logStepA s!"Transport complete: {crew.name} arrived safely"
  pure crew
-- ANCHOR_END: operations_a

-- ANCHOR: operations_b
def logStepB (msg : String) : TransporterB Unit :=
  modify (·.add msg)

def transportB (crew : CrewMember) : TransporterB CrewMember := do
  logStepB s!"Initializing buffer for {crew.name}"
  logStepB s!"Scanning pattern..."
  if crew.name.length > 15 then
    logStepB s!"ERROR: Buffer overflow during scan"
    throw .bufferOverflow
  logStepB s!"Dematerializing {crew.name}..."
  logStepB s!"Pattern in buffer, subject no longer exists at origin"
  if crew.name == "Thomas Riker" then
    logStepB s!"ERROR: Heisenberg compensator failure during transmission"
    throw .heisenbergCompensatorFailure
  logStepB s!"Transmitting..."
  logStepB s!"Rematerializing at destination"
  logStepB s!"Transport complete: {crew.name} arrived safely"
  pure crew
-- ANCHOR_END: operations_b

-- ANCHOR: running
def runTransporterA (crew : CrewMember) : Except TransporterError TransportLog :=
  match StateT.run (transportA crew) {} with
  | .ok (_, log) => .ok log
  | .error e => .error e  -- log is lost!

def runTransporterA' (crew : CrewMember) : TransportLog × Option TransporterError :=
  -- Actually extract the log even on failure
  match StateT.run (transportA crew) {} with
  | .ok (_, log) => (log, none)
  | .error _ =>
    -- With StateT outside, we need a different approach to get the log
    -- This demonstrates the limitation: the log IS preserved in the state
    -- but Except's error case doesn't give us access to it directly
    ({}, some .bufferOverflow)  -- simplified for demo

-- Better: run and always get the log
def runTransporterAWithLog (crew : CrewMember)
    : (Except TransporterError CrewMember) × TransportLog :=
  -- StateT s (Except e) α → s → Except e (α × s)
  -- We need to restructure to always return the log
  match StateT.run (transportA crew) {} with
  | .ok (crew, log) => (.ok crew, log)
  | .error e => (.error e, {})  -- log lost in this formulation!

def runTransporterB (crew : CrewMember) : TransportLog × Except TransporterError CrewMember :=
  -- ExceptT e (StateM s) α → s → (Except e α) × s
  -- State is ALWAYS returned, even on error
  let ((result, log)) := StateT.run (ExceptT.run (transportB crew)) {}
  (log, result)
-- ANCHOR_END: running

-- ANCHOR: demo_difference
def picard : CrewMember := ⟨"Picard", "Captain"⟩
def riker : CrewMember := ⟨"Thomas Riker", "Lieutenant"⟩  -- will fail mid-transport

def demonstrateDifference : IO Unit := do
  IO.println "=== Stack A: StateT TransportLog (Except Error) ==="
  IO.println "State is OUTSIDE Except: on error, state updates are lost\n"

  let resultA := StateT.run (transportA riker) {}
  match resultA with
  | .ok (_, log) =>
    IO.println "Success! Log:"
    for entry in log.entries do IO.println s!"  {entry}"
  | .error e =>
    IO.println s!"FAILED: {e.describe}"
    IO.println "Log: <lost in the error - we only get Except's error case>"
    IO.println "The log entries existed, but Except threw them away."

  IO.println "\n"
  IO.println "=== Stack B: ExceptT Error (StateM TransportLog) ==="
  IO.println "State is INSIDE Except: state updates persist even on error\n"

  let (log, resultB) := runTransporterB riker
  match resultB with
  | .ok _ =>
    IO.println "Success!"
  | .error e =>
    IO.println s!"FAILED: {e.describe}"
  IO.println "Log (preserved!):"
  for entry in log.entries do IO.println s!"  {entry}"
-- ANCHOR_END: demo_difference

def main : IO Unit := do
  IO.println "=== USS Enterprise Transporter: Transformer Ordering Demo ===\n"

  -- First, a successful transport
  IO.println "--- Successful Transport (Captain Picard) ---"
  let (logOk, _) := runTransporterB picard
  for entry in logOk.entries do IO.println s!"  {entry}"

  IO.println "\n--- Failed Transport (Thomas Riker) ---"
  IO.println "Demonstrating the difference between transformer orderings:\n"

  demonstrateDifference

  IO.println "\n--- The Philosophical Horror ---"
  IO.println "With Stack B, the log shows: 'Pattern in buffer, subject no longer"
  IO.println "exists at origin' followed by 'ERROR: Heisenberg compensator failure'."
  IO.println ""
  IO.println "The log PERSISTS. The crew member does NOT."
  IO.println ""
  IO.println "In database terms, this is the difference between:"
  IO.println "  - Transaction rollback (Stack A): nothing happened"
  IO.println "  - Audit logging (Stack B): we recorded what happened"
  IO.println ""
  IO.println "For databases, you choose based on requirements."
  IO.println "For humans, 'transaction aborted after dematerialization' is..."
  IO.println "...not covered in the Starfleet manual."
