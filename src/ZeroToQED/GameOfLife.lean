namespace GameOfLife

-- ANCHOR: grid
abbrev Grid := Array (Array Bool)

def Grid.mk (n m : Nat) (f : Fin n → Fin m → Bool) : Grid :=
  Array.ofFn fun i => Array.ofFn fun j => f i j

def Grid.get (g : Grid) (i j : Nat) : Bool :=
  if h₁ : i < g.size then
    let row := g[i]
    if h₂ : j < row.size then row[j] else false
  else false

def Grid.dead (n m : Nat) : Grid :=
  Array.replicate n (Array.replicate m false)

def Grid.rows (g : Grid) : Nat := g.size
def Grid.cols (g : Grid) : Nat := if h : 0 < g.size then g[0].size else 0
-- ANCHOR_END: grid

-- ANCHOR: neighbors
def Grid.countNeighbors (g : Grid) (i j : Nat) : Nat :=
  let n := g.rows
  let m := g.cols
  let deltas : List (Int × Int) :=
    [(-1, -1), (-1, 0), (-1, 1),
     (0, -1),           (0, 1),
     (1, -1),  (1, 0),  (1, 1)]
  deltas.foldl (fun acc (di, dj) =>
    let ni := (((i : Int) + di + n) % n).toNat
    let nj := (((j : Int) + dj + m) % m).toNat
    if g.get ni nj then acc + 1 else acc) 0
-- ANCHOR_END: neighbors

-- ANCHOR: step
def Grid.step (g : Grid) : Grid :=
  let n := g.rows
  let m := g.cols
  Array.ofFn fun (i : Fin n) => Array.ofFn fun (j : Fin m) =>
    let neighbors := g.countNeighbors i.val j.val
    let alive := g.get i.val j.val
    match alive, neighbors with
    | true, 2 => true
    | true, 3 => true
    | false, 3 => true
    | _, _ => false

def Grid.stepN (g : Grid) : Nat → Grid
  | 0 => g
  | k + 1 => (g.step).stepN k
-- ANCHOR_END: step

-- ANCHOR: patterns
-- John Conway (1937-2020) invented this cellular automaton in 1970.
def blinker : Grid := Grid.mk 5 5 fun i j =>
  (i.val, j.val) ∈ [(1, 2), (2, 2), (3, 2)]

def blinkerPhase2 : Grid := Grid.mk 5 5 fun i j =>
  (i.val, j.val) ∈ [(2, 1), (2, 2), (2, 3)]

def glider : Grid := Grid.mk 6 6 fun i j =>
  (i.val, j.val) ∈ [(0, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

def gliderTranslated : Grid := Grid.mk 6 6 fun i j =>
  (i.val, j.val) ∈ [(1, 2), (2, 3), (3, 1), (3, 2), (3, 3)]

def block : Grid := Grid.mk 4 4 fun i j =>
  (i.val, j.val) ∈ [(1, 1), (1, 2), (2, 1), (2, 2)]
-- ANCHOR_END: patterns

-- ANCHOR: proofs
theorem blinker_oscillates : blinker.step = blinkerPhase2 := by native_decide

theorem blinker_period_2 : blinker.stepN 2 = blinker := by native_decide

theorem glider_translates : glider.stepN 4 = gliderTranslated := by native_decide

theorem block_is_stable : block.step = block := by native_decide
-- ANCHOR_END: proofs

-- ANCHOR: conservation
def Grid.population (g : Grid) : Nat :=
  g.foldl (fun acc row => row.foldl (fun acc cell => if cell then acc + 1 else acc) acc) 0

#eval blinker.population
#eval blinker.step.population
#eval glider.population
#eval glider.step.population
-- ANCHOR_END: conservation

-- ANCHOR: display
def Grid.toString (g : Grid) : String :=
  String.intercalate "\n" <|
    g.toList.map fun row =>
      String.mk <| row.toList.map fun cell =>
        if cell then '#' else '.'

#eval IO.println blinker.toString
#eval IO.println blinker.step.toString
#eval IO.println glider.toString
#eval IO.println (glider.stepN 4).toString
-- ANCHOR_END: display

end GameOfLife
