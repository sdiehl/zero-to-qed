import Mathlib.Tactic

-- ANCHOR: products
inductive Product where
  | HoneyComb
  | SalmonJerky
  | BerryMix
  | GrubBar
  | AcornCrunch
  deriving Repr, DecidableEq

def Product.price : Product → Nat
  | .HoneyComb => 150
  | .SalmonJerky => 200
  | .BerryMix => 100
  | .GrubBar => 125
  | .AcornCrunch => 175

def Product.name : Product → String
  | .HoneyComb => "Honey Comb"
  | .SalmonJerky => "Salmon Jerky"
  | .BerryMix => "Berry Mix"
  | .GrubBar => "Grub Bar"
  | .AcornCrunch => "Acorn Crunch"
-- ANCHOR_END: products

-- ANCHOR: machine
structure Machine (cents : Nat) where mk ::

def insertCoin (coin : Nat) {n : Nat} (_m : Machine n) : Machine (n + coin) := ⟨⟩
def insertDollar {n : Nat} (m : Machine n) : Machine (n + 100) := insertCoin 100 m

def vend (p : Product) {n : Nat} (_m : Machine n) (_h : n ≥ p.price) :
    Product × Machine (n - p.price) := (p, ⟨⟩)

def returnChange {n : Nat} (_m : Machine n) : Nat × Machine 0 := (n, ⟨⟩)

def empty : Machine 0 := ⟨⟩
-- ANCHOR_END: machine

-- ANCHOR: theorems
theorem vend_preserves_state (p : Product) {n : Nat} (m : Machine n) (h : n ≥ p.price) :
    (vend p m h).2 = (⟨⟩ : Machine (n - p.price)) := rfl

theorem insert_return (coin : Nat) : (returnChange (insertCoin coin empty)).1 = coin := by
  simp only [returnChange, Nat.zero_add]
-- ANCHOR_END: theorems

-- ANCHOR: example
def exampleTransaction : Product × Nat := Id.run do
  let m := empty
  let m := insertDollar m
  let m := insertDollar m
  let (snack, m) := vend .BerryMix m (by native_decide)
  let (change, _) := returnChange m
  return (snack, change)
-- ANCHOR_END: example

def formatPrice (c : Nat) : String := s!"${c/100}.{if c%100 < 10 then "0" else ""}{c%100}"

def main : IO Unit := do
  IO.println "=== LEAN VEND 9000 ==="
  for p in [Product.HoneyComb, .SalmonJerky, .BerryMix, .GrubBar, .AcornCrunch] do
    IO.println s!"  {p.name}: {formatPrice p.price}"
  IO.println ""
  let m := empty
  let m := insertDollar m
  let m := insertDollar m
  let (product, m) := vend .BerryMix m (by native_decide)
  let (change, _) := returnChange m
  IO.println s!"Bought: {product.name}, Change: {formatPrice change}"
