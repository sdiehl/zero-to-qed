-- Star Trek Transporter System
-- Run with: lake exe transporter

-- ANCHOR: transporter
inductive TransporterError where
  | bufferOverflow
  | patternDegradation (percent : Nat)
  | heisenbergCompensatorFailure
  | duplicatePattern
  | annularConfinementFailure
  deriving Repr

def TransporterError.describe : TransporterError → String
  | .bufferOverflow => "Pattern buffer overflow - name too long for molecular storage"
  | .patternDegradation p => s!"Pattern degradation at {p}% - signal loss detected"
  | .heisenbergCompensatorFailure => "Heisenberg compensator offline - quantum state uncertain"
  | .duplicatePattern => "Duplicate pattern detected - Thomas Riker situation imminent"
  | .annularConfinementFailure => "Annular confinement beam failure - loss of containment"

structure CrewMember where
  name : String
  rank : String
  species : String := "Human"
  deriving Repr

def initializeBuffer : Except TransporterError Unit :=
  .ok ()

def scanPattern (crew : CrewMember) : Except TransporterError CrewMember :=
  if crew.name.length > 20 then
    .error .bufferOverflow
  else
    .ok crew

def dematerialize (_crew : CrewMember) : Except TransporterError Unit :=
  .ok ()

def transmit : Except TransporterError Unit :=
  .ok ()

def rematerialize (crew : CrewMember) : Except TransporterError CrewMember :=
  .ok crew

def energize (crew : CrewMember) : Except TransporterError CrewMember := do
  initializeBuffer
  let pattern ← scanPattern crew
  dematerialize pattern
  transmit
  rematerialize pattern

def formatResult (crew : CrewMember) (result : Except TransporterError CrewMember) : String :=
  match result with
  | .ok c => s!"[OK] {c.rank} {c.name} transported successfully"
  | .error e => s!"[FAIL] {crew.rank} {crew.name}: {e.describe}"

-- Crew manifest
def picard : CrewMember := ⟨"Jean-Luc Picard", "Captain", "Human"⟩
def redshirt : CrewMember := ⟨"Ensign Expendable McNoLastName", "Ensign", "Human"⟩
-- ANCHOR_END: transporter

def riker : CrewMember := ⟨"William Riker", "Commander", "Human"⟩
def data : CrewMember := ⟨"Data", "Lt. Commander", "Android"⟩
def laforge : CrewMember := ⟨"Geordi La Forge", "Lt. Commander", "Human"⟩
def worf : CrewMember := ⟨"Worf", "Lieutenant", "Klingon"⟩
def troi : CrewMember := ⟨"Deanna Troi", "Counselor", "Betazoid"⟩
def crusher : CrewMember := ⟨"Beverly Crusher", "Commander", "Human"⟩

def main : IO Unit := do
  IO.println "=== USS Enterprise NCC-1701-D Transporter System ==="
  IO.println ""
  IO.println "Initializing transporter sequence..."
  IO.println ""

  let crew := [picard, riker, data, laforge, worf, troi, crusher, redshirt]

  IO.println "--- Transport Log ---"
  for member in crew do
    let result := energize member
    IO.println (formatResult member result)

  IO.println ""
  IO.println "Transport sequence complete."
  IO.println ""
  IO.println "Note: The transporter works by disassembling humans at the molecular"
  IO.println "level and reassembling them elsewhere. If formal verification ever"
  IO.println "finds a practical purpose, this might be it - assuming we can get"
  IO.println "the Heisenberg compensator working."
