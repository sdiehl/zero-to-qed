import Mathlib.Tactic.Ring

namespace StackMachine

-- ANCHOR: ops
inductive Op where
  | push : Int → Op
  | pop : Op
  | add : Op
  | mul : Op
  | dup : Op
  deriving Repr, DecidableEq
-- ANCHOR_END: ops

-- ANCHOR: run
def run : List Op → List Int → List Int
  | [], stack => stack
  | .push n :: ops, stack => run ops (n :: stack)
  | .pop :: ops, _ :: stack => run ops stack
  | .pop :: ops, [] => run ops []
  | .add :: ops, b :: a :: stack => run ops ((a + b) :: stack)
  | .add :: ops, stack => run ops stack
  | .mul :: ops, b :: a :: stack => run ops ((a * b) :: stack)
  | .mul :: ops, stack => run ops stack
  | .dup :: ops, x :: stack => run ops (x :: x :: stack)
  | .dup :: ops, [] => run ops []
-- ANCHOR_END: run

-- ANCHOR: examples
#eval run [.push 3, .push 4, .add] []
#eval run [.push 3, .push 4, .mul] []
#eval run [.push 5, .dup, .mul] []
#eval run [.push 10, .push 3, .pop] []
-- ANCHOR_END: examples

-- ANCHOR: composition
theorem run_append (p1 p2 : List Op) (s : List Int) :
    run (p1 ++ p2) s = run p2 (run p1 s) := by
  induction p1 generalizing s with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | push n => exact ih _
    | pop => cases s <;> exact ih _
    | add => match s with
      | [] | [_] => exact ih _
      | _ :: _ :: _ => exact ih _
    | mul => match s with
      | [] | [_] => exact ih _
      | _ :: _ :: _ => exact ih _
    | dup => cases s <;> exact ih _
-- ANCHOR_END: composition

-- ANCHOR: effect
def effect : Op → Int
  | .push _ => 1
  | .pop => -1
  | .add => -1
  | .mul => -1
  | .dup => 1

def totalEffect : List Op → Int
  | [] => 0
  | op :: ops => effect op + totalEffect ops

theorem effect_append (p1 p2 : List Op) :
    totalEffect (p1 ++ p2) = totalEffect p1 + totalEffect p2 := by
  induction p1 with
  | nil => simp [totalEffect]
  | cons op ops ih => simp [totalEffect, ih]; ring
-- ANCHOR_END: effect

-- ANCHOR: depth
def minDepth : Op → Nat
  | .push _ => 0
  | .pop => 1
  | .add => 2
  | .mul => 2
  | .dup => 1

def isSafe : Nat → List Op → Bool
  | _, [] => true
  | d, op :: ops =>
    d ≥ minDepth op && isSafe ((d : Int) + effect op).toNat ops

#eval isSafe 0 [.push 3, .push 4, .add]
#eval isSafe 0 [.add]
#eval isSafe 2 [.add]
#eval isSafe 0 [.push 1, .pop, .pop]
-- ANCHOR_END: depth

-- ANCHOR: equivalence
theorem add_comm (n m : Int) (rest : List Op) (s : List Int) :
    run (.push n :: .push m :: .add :: rest) s =
    run (.push m :: .push n :: .add :: rest) s := by
  simp [run, Int.add_comm]

theorem mul_comm (n m : Int) (rest : List Op) (s : List Int) :
    run (.push n :: .push m :: .mul :: rest) s =
    run (.push m :: .push n :: .mul :: rest) s := by
  simp [run, Int.mul_comm]

theorem dup_add_eq_double (n : Int) (rest : List Op) (s : List Int) :
    run (.push n :: .dup :: .add :: rest) s =
    run (.push (n + n) :: rest) s := by
  simp [run]

theorem dup_mul_eq_square (n : Int) (rest : List Op) (s : List Int) :
    run (.push n :: .dup :: .mul :: rest) s =
    run (.push (n * n) :: rest) s := by
  simp [run]
-- ANCHOR_END: equivalence

-- ANCHOR: universal
example : ∀ p1 p2 s, run (p1 ++ p2) s = run p2 (run p1 s) := run_append
example : ∀ p1 p2, totalEffect (p1 ++ p2) = totalEffect p1 + totalEffect p2 := effect_append
-- ANCHOR_END: universal

end StackMachine
