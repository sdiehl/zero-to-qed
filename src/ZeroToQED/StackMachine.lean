/-
# Stack Machine Verification

This module demonstrates verification-guided development following the Cedar approach.
We transcribe a Rust implementation into Lean, prove properties about the Lean model,
and the proofs transfer because both systems produce identical execution traces.
-/

namespace StackMachine

-- ANCHOR: ops
inductive Op where
  | push : Int → Op
  | pop : Op
  | add : Op
  | mul : Op
  | dup : Op
  | swap : Op
  deriving Repr, DecidableEq
-- ANCHOR_END: ops

-- ANCHOR: state
structure State where
  stack : List Int
  valid : Bool
  deriving Repr, DecidableEq
-- ANCHOR_END: state

-- ANCHOR: step
def step (s : State) (op : Op) : State :=
  if !s.valid then { stack := s.stack, valid := false }
  else match op with
    | .push n => { stack := n :: s.stack, valid := true }
    | .pop => match s.stack with
        | [] => { stack := [], valid := false }
        | _ :: rest => { stack := rest, valid := true }
    | .add => match s.stack with
        | b :: a :: rest => { stack := (a + b) :: rest, valid := true }
        | _ => { stack := s.stack, valid := false }
    | .mul => match s.stack with
        | b :: a :: rest => { stack := (a * b) :: rest, valid := true }
        | _ => { stack := s.stack, valid := false }
    | .dup => match s.stack with
        | [] => { stack := [], valid := false }
        | x :: rest => { stack := x :: x :: rest, valid := true }
    | .swap => match s.stack with
        | b :: a :: rest => { stack := a :: b :: rest, valid := true }
        | _ => { stack := s.stack, valid := false }
-- ANCHOR_END: step

-- ANCHOR: run
def initial : State := { stack := [], valid := true }

def run (program : List Op) : State :=
  program.foldl step initial

def runFrom (s : State) (program : List Op) : State :=
  program.foldl step s
-- ANCHOR_END: run

-- ANCHOR: trace
def trace (program : List Op) : List State :=
  let rec go (s : State) : List Op → List State
    | [] => [s]
    | op :: rest => s :: go (step s op) rest
  go initial program
-- ANCHOR_END: trace

-- ANCHOR: trace_examples
#eval trace [.push 3, .push 4, .add]
#eval trace [.push 5, .dup, .add]
#eval trace [.pop]
#eval trace [.push 1, .add]
-- ANCHOR_END: trace_examples

-- ANCHOR: depth
def depth (s : State) : Nat := s.stack.length
-- ANCHOR_END: depth

-- ANCHOR: spec_depth
def opEffect : Op → Int
  | .push _ => 1
  | .pop => -1
  | .add => -1
  | .mul => -1
  | .dup => 1
  | .swap => 0

def opRequires : Op → Nat
  | .push _ => 0
  | .pop => 1
  | .add => 2
  | .mul => 2
  | .dup => 1
  | .swap => 2
-- ANCHOR_END: spec_depth

-- ANCHOR: bisim_basic
theorem push_increases_depth (s : State) (n : Int) (h : s.valid) :
    depth (step s (.push n)) = depth s + 1 := by
  simp [step, h, depth]

theorem add_decreases_depth_concrete :
    depth (step { stack := [4, 3], valid := true } .add) =
    depth { stack := [4, 3], valid := true } - 1 := by native_decide

theorem swap_preserves_depth_concrete :
    depth (step { stack := [4, 3], valid := true } .swap) =
    depth { stack := [4, 3], valid := true } := by native_decide
-- ANCHOR_END: bisim_basic

-- ANCHOR: underflow_proofs
theorem pop_empty_fails : (step { stack := [], valid := true } .pop).valid = false := by
  native_decide

theorem add_one_fails : (step { stack := [1], valid := true } .add).valid = false := by
  native_decide

theorem invalid_propagates (s : State) (op : Op) (h : !s.valid) :
    (step s op).valid = false := by
  simp [step, h]
-- ANCHOR_END: underflow_proofs

-- ANCHOR: concrete_bisim
theorem exec_push_add :
    run [.push 3, .push 4, .add] = { stack := [7], valid := true } := by native_decide

theorem exec_push_mul :
    run [.push 3, .push 4, .mul] = { stack := [12], valid := true } := by native_decide

theorem exec_dup_add :
    run [.push 5, .dup, .add] = { stack := [10], valid := true } := by native_decide

theorem exec_swap :
    run [.push 10, .push 3, .swap] = { stack := [10, 3], valid := true } := by native_decide

theorem exec_complex :
    run [.push 3, .push 4, .add, .push 2, .mul] = { stack := [14], valid := true } := by
  native_decide

theorem exec_underflow_pop :
    run [.pop] = { stack := [], valid := false } := by native_decide

theorem exec_underflow_add :
    run [.push 1, .add] = { stack := [1], valid := false } := by native_decide

theorem exec_underflow_propagates :
    run [.pop, .push 1, .push 2, .add] = { stack := [], valid := false } := by native_decide
-- ANCHOR_END: concrete_bisim

-- ANCHOR: trace_bisim
theorem trace_push_add :
    trace [.push 3, .push 4, .add] =
      [ { stack := [], valid := true },
        { stack := [3], valid := true },
        { stack := [4, 3], valid := true },
        { stack := [7], valid := true } ] := by native_decide

theorem trace_underflow :
    trace [.pop, .push 1] =
      [ { stack := [], valid := true },
        { stack := [], valid := false },
        { stack := [], valid := false } ] := by native_decide
-- ANCHOR_END: trace_bisim

-- ANCHOR: invariants
theorem valid_after_push (s : State) (n : Int) (h : s.valid) :
    (step s (.push n)).valid = true := by
  simp [step, h]

theorem push_sequence_valid_1 :
    (run [.push 1]).valid = true := by native_decide

theorem push_sequence_valid_3 :
    (run [.push 1, .push 2, .push 3]).valid = true := by native_decide

theorem depth_after_3_pushes :
    depth (run [.push 1, .push 2, .push 3]) = 3 := by native_decide

theorem depth_after_push_pop :
    depth (run [.push 1, .push 2, .pop]) = 1 := by native_decide
-- ANCHOR_END: invariants

-- ANCHOR: verified_programs
def program1 : List Op := [.push 3, .push 4, .add]
def program2 : List Op := [.push 5, .dup, .add]
def program3 : List Op := [.push 3, .push 4, .add, .push 2, .mul]
def program4 : List Op := [.push 10, .push 3, .swap, .pop]

theorem program1_correct : run program1 = { stack := [7], valid := true } := by native_decide
theorem program2_correct : run program2 = { stack := [10], valid := true } := by native_decide
theorem program3_correct : run program3 = { stack := [14], valid := true } := by native_decide
theorem program4_correct : run program4 = { stack := [3], valid := true } := by native_decide

theorem program1_trace_length : (trace program1).length = 4 := by native_decide
theorem program2_trace_length : (trace program2).length = 4 := by native_decide
-- ANCHOR_END: verified_programs

end StackMachine
