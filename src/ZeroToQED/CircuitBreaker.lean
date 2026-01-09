import Lean

namespace CircuitBreaker

-- ANCHOR: config
structure Config where
  threshold : Nat
  timeout : Nat
  deriving DecidableEq, Repr
-- ANCHOR_END: config

-- ANCHOR: state
inductive State where
  | closed (failures : Nat) : State
  | opened (openedAt : Nat) : State
  | halfOpen : State
  deriving DecidableEq, Repr
-- ANCHOR_END: state

-- ANCHOR: event
inductive Event where
  | success : Event
  | failure (time : Nat) : Event
  | tick (time : Nat) : Event
  | probeSuccess (time : Nat) : Event
  | probeFailure (time : Nat) : Event
  deriving DecidableEq, Repr
-- ANCHOR_END: event

-- ANCHOR: step
def step (cfg : Config) (s : State) (e : Event) : State :=
  match s, e with
  | .closed _, .success => .closed 0
  | .closed failures, .failure time =>
    if failures + 1 >= cfg.threshold then .opened time
    else .closed (failures + 1)
  | .opened openedAt, .tick time =>
    if time - openedAt >= cfg.timeout then .halfOpen
    else .opened openedAt
  | .halfOpen, .probeSuccess _ => .closed 0
  | .halfOpen, .probeFailure time => .opened time
  | s, _ => s
-- ANCHOR_END: step

def initial : State := .closed 0

-- ANCHOR: invariant
def Invariant (cfg : Config) : State → Prop
  | .closed failures => failures < cfg.threshold
  | .opened _ => True
  | .halfOpen => True

theorem initial_invariant (cfg : Config) (h : cfg.threshold > 0) :
    Invariant cfg initial := h

theorem step_preserves_invariant (cfg : Config) (s : State) (e : Event)
    (hinv : Invariant cfg s) (hpos : cfg.threshold > 0) :
    Invariant cfg (step cfg s e) := by
  cases s with
  | closed failures =>
    cases e with
    | success => simp [step, Invariant, hpos]
    | failure time =>
      simp only [step]
      split
      · simp [Invariant]
      · simp [Invariant]; omega
    | tick _ => simp [step, Invariant]; exact hinv
    | probeSuccess _ => simp [step, Invariant]; exact hinv
    | probeFailure _ => simp [step, Invariant]; exact hinv
  | opened openedAt =>
    cases e with
    | tick time =>
      simp only [step]
      split <;> simp [Invariant]
    | _ => simp [step, Invariant]
  | halfOpen =>
    cases e with
    | probeSuccess _ => simp [step, Invariant, hpos]
    | probeFailure _ => simp [step, Invariant]
    | _ => simp [step, Invariant]
-- ANCHOR_END: invariant

-- ANCHOR: theorems
theorem success_resets (cfg : Config) (f : Nat) :
    step cfg (.closed f) .success = .closed 0 := rfl

theorem threshold_trips (cfg : Config) (f t : Nat) (h : f + 1 >= cfg.threshold) :
    step cfg (.closed f) (.failure t) = .opened t := by simp [step, h]

theorem below_threshold_increments (cfg : Config) (f t : Nat) (h : f + 1 < cfg.threshold) :
    step cfg (.closed f) (.failure t) = .closed (f + 1) := by
  simp [step]; omega

theorem timeout_transitions (cfg : Config) (o t : Nat) (h : t - o >= cfg.timeout) :
    step cfg (.opened o) (.tick t) = .halfOpen := by simp [step, h]

theorem probe_success_closes (cfg : Config) (t : Nat) :
    step cfg .halfOpen (.probeSuccess t) = .closed 0 := rfl

theorem probe_failure_reopens (cfg : Config) (t : Nat) :
    step cfg .halfOpen (.probeFailure t) = .opened t := rfl
-- ANCHOR_END: theorems

-- ANCHOR: uniformity
def sameStateKind : State → State → Bool
  | .closed _, .closed _ => true
  | .opened _, .opened _ => true
  | .halfOpen, .halfOpen => true
  | _, _ => false

def sameEventKind : Event → Event → Bool
  | .success, .success => true
  | .failure _, .failure _ => true
  | .tick _, .tick _ => true
  | .probeSuccess _, .probeSuccess _ => true
  | .probeFailure _, .probeFailure _ => true
  | _, _ => false

structure ComparisonResults where
  thresholdReached : Bool
  timeoutElapsed : Bool
  deriving DecidableEq, Repr

def getComparisons (cfg : Config) (s : State) (e : Event) : ComparisonResults :=
  match s, e with
  | .closed f, .failure _ => ⟨f + 1 >= cfg.threshold, false⟩
  | .opened o, .tick t => ⟨false, t - o >= cfg.timeout⟩
  | _, _ => ⟨false, false⟩

theorem uniformity (cfg₁ cfg₂ : Config) (s₁ s₂ : State) (e₁ e₂ : Event)
    (hsame_state : sameStateKind s₁ s₂)
    (hsame_event : sameEventKind e₁ e₂)
    (hsame_cmp : getComparisons cfg₁ s₁ e₁ = getComparisons cfg₂ s₂ e₂) :
    sameStateKind (step cfg₁ s₁ e₁) (step cfg₂ s₂ e₂) := by
  cases s₁ <;> cases s₂ <;> simp_all [sameStateKind]
  all_goals cases e₁ <;> cases e₂ <;> simp_all [sameEventKind, step, getComparisons]
  case closed.closed.failure.failure f₁ f₂ t₁ t₂ =>
    by_cases h₁ : f₁ + 1 >= cfg₁.threshold <;>
    by_cases h₂ : f₂ + 1 >= cfg₂.threshold <;>
    simp only [h₂, ↓reduceIte] <;> simp_all
  case opened.opened.tick.tick o₁ o₂ t₁ t₂ =>
    by_cases h₁ : t₁ - o₁ >= cfg₁.timeout <;>
    by_cases h₂ : t₂ - o₂ >= cfg₂.timeout <;>
    simp only [h₂, ↓reduceIte] <;> simp_all
-- ANCHOR_END: uniformity

-- ANCHOR: bounds
structure Bounds where
  maxThreshold : Nat := 4
  maxTimeout : Nat := 10
  maxTime : Nat := 20
-- ANCHOR_END: bounds

def enumerateStates (threshold maxTime : Nat) : List State :=
  (List.range threshold).map .closed ++
  (List.range (maxTime + 1)).map .opened ++
  [.halfOpen]

def enumerateEvents (maxTime : Nat) : List Event :=
  [.success] ++
  (List.range (maxTime + 1)).map .failure ++
  (List.range (maxTime + 1)).map .tick ++
  (List.range (maxTime + 1)).map .probeSuccess ++
  (List.range (maxTime + 1)).map .probeFailure

-- ANCHOR: testcase
structure TestCase where
  threshold : Nat
  timeout : Nat
  state : State
  event : Event
  expected : State
  deriving Repr
-- ANCHOR_END: testcase

def exhaustiveTests (b : Bounds) : List TestCase := Id.run do
  let mut tests : List TestCase := []
  for threshold in List.range' 1 b.maxThreshold do
    for timeout in List.range' 1 b.maxTimeout do
      let cfg : Config := ⟨threshold, timeout⟩
      for s in enumerateStates threshold b.maxTime do
        for e in enumerateEvents b.maxTime do
          tests := ⟨threshold, timeout, s, e, step cfg s e⟩ :: tests
  return tests

open Lean in
def State.toJson : State → Json
  | .closed n => .mkObj [("Closed", .num n)]
  | .opened n => .mkObj [("Open", .num n)]
  | .halfOpen => .str "HalfOpen"

open Lean in
def Event.toJson : Event → Json
  | .success => .str "Success"
  | .failure n => .mkObj [("Failure", .num n)]
  | .tick n => .mkObj [("Tick", .num n)]
  | .probeSuccess n => .mkObj [("ProbeSuccess", .num n)]
  | .probeFailure n => .mkObj [("ProbeFailure", .num n)]

open Lean in
def TestCase.toJson (tc : TestCase) : Json :=
  .mkObj [
    ("threshold", .num tc.threshold),
    ("timeout", .num tc.timeout),
    ("state", tc.state.toJson),
    ("event", tc.event.toJson),
    ("expected", tc.expected.toJson)
  ]

open Lean in
def exportTests (tests : List TestCase) : Json :=
  .arr (tests.map TestCase.toJson).toArray

def writeTests (path : System.FilePath) (b : Bounds) : IO Unit := do
  let tests := exhaustiveTests b
  IO.FS.writeFile path (exportTests tests).compress
  IO.println s!"Exported {tests.length} test cases to {path}"

-- ANCHOR: simulate
def simulate (cfg : Config) (events : List Event) : List State :=
  let rec go (s : State) (es : List Event) (acc : List State) : List State :=
    match es with
    | [] => (s :: acc).reverse
    | e :: rest => go (step cfg s e) rest (s :: acc)
  go initial events []
-- ANCHOR_END: simulate

-- ANCHOR: example
#eval do
  let cfg : Config := ⟨3, 100⟩
  let events := [Event.failure 10, .failure 20, .failure 30, .tick 50, .tick 150, .probeSuccess 160]
  let trace := simulate cfg events
  IO.println s!"Trace: {repr trace}"
-- ANCHOR_END: example

def defaultBounds : Bounds := { maxThreshold := 4, maxTimeout := 10, maxTime := 20 }

#eval do
  let n := (exhaustiveTests defaultBounds).length
  IO.println s!"Exhaustive tests: {n} cases"

#eval writeTests "examples/circuit-breaker/testdata/exhaustive_tests.json" defaultBounds

end CircuitBreaker
