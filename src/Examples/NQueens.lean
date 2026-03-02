-- ANCHOR: types
abbrev Placement := List Nat

def attacks (r1 c1 r2 c2 : Nat) : Bool :=
  c1 == c2 || (if r1 ≥ r2 then r1 - r2 else r2 - r1) == (if c1 ≥ c2 then c1 - c2 else c2 - c1)

def isSafeAux (newRow col : Nat) : Placement → Nat → Bool
  | [], _ => true
  | qc :: rest, row => !attacks newRow col row qc && isSafeAux newRow col rest (row + 1)

def isSafe (col : Nat) (p : Placement) : Bool := isSafeAux p.length col p 0
-- ANCHOR_END: types

-- ANCHOR: valid
def Valid (n : Nat) (p : Placement) : Prop :=
  p.length = n ∧ p.all (· < n) ∧
  ∀ i j, i < j → j < p.length → !attacks i p[i]! j p[j]!

structure Board (n : Nat) where
  placement : Placement
  valid : Valid n placement
-- ANCHOR_END: valid

-- ANCHOR: verify
def verify (n : Nat) (p : Placement) : Bool :=
  p.length == n && p.all (· < n) &&
  (List.range p.length).all fun i =>
    (List.range p.length).all fun j => i >= j || !attacks i p[i]! j p[j]!
-- ANCHOR_END: verify

-- ANCHOR: solve
partial def solve (n : Nat) (p : Placement := []) : Option Placement :=
  if p.length == n then some p
  else (List.range n).findSome? fun c => if isSafe c p then solve n (p ++ [c]) else none
-- ANCHOR_END: solve

-- ANCHOR: theorem
theorem board_length {n : Nat} (b : Board n) : b.placement.length = n := b.valid.1
-- ANCHOR_END: theorem

def showBoard (n : Nat) (p : Placement) : String :=
  String.intercalate "\n" <| (List.range n).map fun r =>
    String.ofList <| (List.range n).map fun c => if p[r]! == c then 'Q' else '.'

def main : IO Unit := do
  IO.println "4-Queens:"
  if let some p := solve 4 then IO.println (showBoard 4 p)
  IO.println "\n8-Queens:"
  if let some p := solve 8 then IO.println (showBoard 8 p)
  IO.println s!"\nVerified 8-Queens: {verify 8 ((solve 8).getD [])}"
