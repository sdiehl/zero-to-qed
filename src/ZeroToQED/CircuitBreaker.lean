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
  -- Step 1: Case split on state constructors. Off-diagonal cases (e.g., closed vs opened)
  -- are contradictions since hsame_state requires matching constructors.
  cases s₁ <;> cases s₂ <;> simp_all [sameStateKind]
  -- Step 2: For each diagonal case (closed/closed, opened/opened, halfOpen/halfOpen),
  -- split on event constructors. Again, off-diagonal cases contradict hsame_event.
  all_goals cases e₁ <;> cases e₂ <;> simp_all [sameEventKind, step, getComparisons]
  -- Step 3: Two cases remain where step branches on comparisons:
  -- (closed, failure) branches on threshold check
  case closed.closed.failure.failure f₁ f₂ t₁ t₂ =>
    -- hsame_cmp says both threshold comparisons have the same boolean result.
    -- Case split on whether each threshold is reached.
    by_cases h₁ : f₁ + 1 >= cfg₁.threshold <;>
    by_cases h₂ : f₂ + 1 >= cfg₂.threshold <;>
    -- When h₁ and h₂ disagree, hsame_cmp gives a contradiction.
    -- When they agree, both step to the same constructor.
    simp only [h₂, ↓reduceIte] <;> simp_all
  -- (opened, tick) branches on timeout check
  case opened.opened.tick.tick o₁ o₂ t₁ t₂ =>
    -- Same logic: hsame_cmp forces timeout comparisons to agree.
    by_cases h₁ : t₁ - o₁ >= cfg₁.timeout <;>
    by_cases h₂ : t₂ - o₂ >= cfg₂.timeout <;>
    simp only [h₂, ↓reduceIte] <;> simp_all
-- ANCHOR_END: uniformity

-- ANCHOR: correctness
theorem correctness (cfg : Config) (hpos : cfg.threshold > 0) :
    (Invariant cfg initial) ∧
    (∀ s e, Invariant cfg s → Invariant cfg (step cfg s e)) ∧
    (∀ cfg₂ s₁ s₂ e₁ e₂,
      sameStateKind s₁ s₂ → sameEventKind e₁ e₂ →
      getComparisons cfg s₁ e₁ = getComparisons cfg₂ s₂ e₂ →
      sameStateKind (step cfg s₁ e₁) (step cfg₂ s₂ e₂)) :=
  ⟨initial_invariant cfg hpos,
   fun s e hinv => step_preserves_invariant cfg s e hinv hpos,
   fun _ _ _ _ _ hs he hc => uniformity cfg _ _ _ _ _ hs he hc⟩
-- ANCHOR_END: correctness

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

-- ANCHOR: bmc_run
/-- Run a whole execution: feed a list of events to `step`, starting from `initial`. -/
def run (cfg : Config) (events : List Event) : State :=
  events.foldl (step cfg) initial
-- ANCHOR_END: bmc_run

-- ANCHOR: bmc_unroll
/-- One execution prefix: the events consumed so far and the state they lead to. -/
structure Run where
  events : List Event
  state : State
  deriving Repr

/-- Keep one witness execution per distinct state. Earlier (shorter) runs win. -/
def addRun (acc : List Run) (r : Run) : List Run :=
  if acc.any (·.state == r.state) then acc else acc ++ [r]

/-- Unroll the transition relation `k` times over a finite event alphabet.
    The result holds every state reachable in at most `k` steps, each paired
    with a shortest execution that reaches it. -/
def unroll (cfg : Config) (alphabet : List Event) : Nat → List Run
  | 0 => [⟨[], initial⟩]
  | k + 1 =>
    let prev := unroll cfg alphabet k
    let next := prev.flatMap fun r =>
      alphabet.map fun e => ⟨r.events ++ [e], step cfg r.state e⟩
    (prev ++ next).foldl addRun []
-- ANCHOR_END: bmc_unroll

-- ANCHOR: bmc_query
/-- The bounded model checking query: is there an execution of at most `k`
    steps over `alphabet` that ends in a state violating `P`? If so, return it. -/
def bmc (cfg : Config) (alphabet : List Event) (P : State → Bool) (k : Nat) :
    Option (List Event) :=
  ((unroll cfg alphabet k).find? fun r => !P r.state).map (·.events)

/-- A concrete instance: threshold 3, timeout 5, and every event with a
    timestamp up to 5. -/
def cfg₀ : Config := ⟨3, 5⟩
def alphabet₀ : List Event := enumerateEvents 5

/-- A property that sounds plausible and is false: the breaker never half-opens. -/
def neverHalfOpen : State → Bool
  | .halfOpen => false
  | _ => true

/-- info: none -/
#guard_msgs in
#eval bmc cfg₀ alphabet₀ neverHalfOpen 3

/--
info: some [CircuitBreaker.Event.failure 0,
 CircuitBreaker.Event.failure 0,
 CircuitBreaker.Event.failure 0,
 CircuitBreaker.Event.tick 5]
-/
#guard_msgs in
#eval bmc cfg₀ alphabet₀ neverHalfOpen 4
-- ANCHOR_END: bmc_query

-- ANCHOR: bmc_saturation
/-- The invariant as a decidable check. -/
def invariantB (cfg : Config) : State → Bool
  | .closed f => f < cfg.threshold
  | _ => true

/-- No execution of at most six steps violates the invariant. A bounded claim. -/
theorem no_short_counterexample : bmc cfg₀ alphabet₀ (invariantB cfg₀) 6 = none := by
  decide +kernel

/-- The states reachable within four steps. -/
def reach₀ : List State := (unroll cfg₀ alphabet₀ 4).map (·.state)

/-- Unrolling a fifth time finds nothing new: the reachable set has saturated,
    so four is a completeness threshold for this instance. -/
theorem saturated : (unroll cfg₀ alphabet₀ 5).map (·.state) = reach₀ := by
  decide +kernel
-- ANCHOR_END: bmc_saturation

-- ANCHOR: bmc_soundness
theorem foldl_mem (cfg : Config) (alphabet : List Event) (R : List State)
    (hstep : ∀ s ∈ R, ∀ e ∈ alphabet, step cfg s e ∈ R) :
    ∀ (es : List Event) (s : State), s ∈ R → (∀ e ∈ es, e ∈ alphabet) →
      es.foldl (step cfg) s ∈ R
  | [], _, hs, _ => hs
  | e :: es, s, hs, hall =>
    foldl_mem cfg alphabet R hstep es (step cfg s e)
      (hstep s hs e (hall e (List.mem_cons_self ..)))
      (fun e' he' => hall e' (List.mem_cons_of_mem _ he'))

/-- Any set of states that contains `initial` and is closed under `step`
    over the alphabet contains the final state of every execution, of any length. -/
theorem closed_set_sound (cfg : Config) (alphabet : List Event) (R : List State)
    (hinit : initial ∈ R)
    (hstep : ∀ s ∈ R, ∀ e ∈ alphabet, step cfg s e ∈ R)
    (es : List Event) (hes : ∀ e ∈ es, e ∈ alphabet) :
    run cfg es ∈ R :=
  foldl_mem cfg alphabet R hstep es initial hinit hes
-- ANCHOR_END: bmc_soundness

-- ANCHOR: bmc_unbounded
instance (cfg : Config) (s : State) : Decidable (Invariant cfg s) :=
  match s with
  | .closed f => inferInstanceAs (Decidable (f < cfg.threshold))
  | .opened _ => inferInstanceAs (Decidable True)
  | .halfOpen => inferInstanceAs (Decidable True)

/-- The three facts about `reach₀` that the kernel checks by computation. -/
theorem reach₀_init : initial ∈ reach₀ := by decide +kernel
theorem reach₀_closed : ∀ s ∈ reach₀, ∀ e ∈ alphabet₀, step cfg₀ s e ∈ reach₀ := by
  decide +kernel
theorem reach₀_inv : ∀ s ∈ reach₀, Invariant cfg₀ s := by decide +kernel

/-- The bounded result, lifted: every execution over `alphabet₀`, however long,
    ends in a state satisfying the invariant. -/
theorem invariant_all_runs (es : List Event) (hes : ∀ e ∈ es, e ∈ alphabet₀) :
    Invariant cfg₀ (run cfg₀ es) :=
  reach₀_inv _ (closed_set_sound cfg₀ alphabet₀ reach₀ reach₀_init reach₀_closed es hes)

def isOpen : State → Bool
  | .opened _ => true
  | _ => false

def isClosed : State → Bool
  | .closed _ => true
  | _ => false

/-- A transition property no single-state invariant can express: an open
    breaker never closes in one step. Checked on the saturated set. -/
theorem reach₀_no_open_to_closed :
    ∀ s ∈ reach₀, ∀ e ∈ alphabet₀, ¬(isOpen s ∧ isClosed (step cfg₀ s e)) := by
  decide +kernel

theorem never_open_to_closed (es : List Event) (hes : ∀ e ∈ es, e ∈ alphabet₀)
    (e : Event) (he : e ∈ alphabet₀) :
    ¬(isOpen (run cfg₀ es) ∧ isClosed (step cfg₀ (run cfg₀ es) e)) :=
  reach₀_no_open_to_closed _
    (closed_set_sound cfg₀ alphabet₀ reach₀ reach₀_init reach₀_closed es hes) e he
-- ANCHOR_END: bmc_unbounded

-- ANCHOR: trace_tests
/-- A multi-step test: an execution and the full sequence of states it visits. -/
structure TraceCase where
  threshold : Nat
  timeout : Nat
  events : List Event
  expected : List State
  deriving Repr

/-- For each configuration, take the saturated unrolling, and extend every
    witness execution by every event. Each trace reaches a reachable state by
    a real execution and then exercises one more transition from it. -/
def traceTests (maxThreshold maxTimeout maxTime depth : Nat) : List TraceCase := Id.run do
  let alphabet := enumerateEvents maxTime
  let mut tests : List TraceCase := []
  for threshold in List.range' 1 maxThreshold do
    for timeout in List.range' 1 maxTimeout do
      let cfg : Config := ⟨threshold, timeout⟩
      for r in unroll cfg alphabet depth do
        for e in alphabet do
          let events := r.events ++ [e]
          tests := ⟨threshold, timeout, events, simulate cfg events⟩ :: tests
  return tests
-- ANCHOR_END: trace_tests

open Lean in
def TraceCase.toJson (tc : TraceCase) : Json :=
  .mkObj [
    ("threshold", .num tc.threshold),
    ("timeout", .num tc.timeout),
    ("events", .arr (tc.events.map Event.toJson).toArray),
    ("expected", .arr (tc.expected.map State.toJson).toArray)
  ]

open Lean in
def writeTraceTests (path : System.FilePath) : IO Unit := do
  let tests := traceTests 3 3 5 8
  IO.FS.writeFile path (Json.arr (tests.map TraceCase.toJson).toArray).compress
  IO.println s!"Exported {tests.length} trace tests to {path}"

#eval writeTraceTests "examples/circuit-breaker/testdata/trace_tests.json"

end CircuitBreaker
