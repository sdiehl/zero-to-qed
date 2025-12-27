-- Magic: The Gathering Mana System
-- Run with: lake exe mtg

-- ANCHOR: mtg_mana
inductive ManaColor where
  | white | blue | black | red | green | colorless
  deriving Repr, DecidableEq

structure ManaCost where
  white : Nat := 0
  blue : Nat := 0
  black : Nat := 0
  red : Nat := 0
  green : Nat := 0
  colorless : Nat := 0
  deriving Repr

structure ManaPool where
  white : Nat := 0
  blue : Nat := 0
  black : Nat := 0
  red : Nat := 0
  green : Nat := 0
  colorless : Nat := 0
  deriving Repr

def ManaPool.total (p : ManaPool) : Nat :=
  p.white + p.blue + p.black + p.red + p.green + p.colorless

def ManaPool.canPay (pool : ManaPool) (cost : ManaCost) : Bool :=
  pool.white >= cost.white &&
  pool.blue >= cost.blue &&
  pool.black >= cost.black &&
  pool.red >= cost.red &&
  pool.green >= cost.green &&
  pool.total >= cost.white + cost.blue + cost.black +
                cost.red + cost.green + cost.colorless

structure Card where
  name : String
  cost : ManaCost
  description : String

def lightningBolt : Card :=
  { name := "Lightning Bolt"
    cost := { red := 1 }
    description := "Deal 3 damage to any target" }

def counterspell : Card :=
  { name := "Counterspell"
    cost := { blue := 2 }
    description := "Counter target spell" }

def wrathOfGod : Card :=
  { name := "Wrath of God"
    cost := { white := 2, colorless := 2 }
    description := "Destroy all creatures" }

-- ANCHOR_END: mtg_mana

def llanowarElves : Card :=
  { name := "Llanowar Elves"
    cost := { green := 1 }
    description := "Tap: Add G" }

def blackLotus : Card :=
  { name := "Black Lotus"
    cost := {}
    description := "Tap, Sacrifice: Add three mana of any one color" }

def formatCost (c : ManaCost) : String :=
  let parts := #[
    if c.colorless > 0 then s!"{c.colorless}" else "",
    String.mk (List.replicate c.white 'W'),
    String.mk (List.replicate c.blue 'U'),
    String.mk (List.replicate c.black 'B'),
    String.mk (List.replicate c.red 'R'),
    String.mk (List.replicate c.green 'G')
  ]
  let result := String.join (parts.toList.filter (· ≠ ""))
  if result.isEmpty then "0" else result

def formatPool (p : ManaPool) : String :=
  s!"W:{p.white} U:{p.blue} B:{p.black} R:{p.red} G:{p.green} C:{p.colorless}"

def checkCard (pool : ManaPool) (card : Card) : IO Unit := do
  let canCast := pool.canPay card.cost
  let symbol := if canCast then "[OK]" else "[X] "
  IO.println s!"{symbol} {card.name} ({formatCost card.cost})"

def main : IO Unit := do
  IO.println "=== Magic: The Gathering Mana System ==="
  IO.println ""

  let pool : ManaPool := { blue := 3, white := 2, red := 1 }
  IO.println s!"Mana Pool: {formatPool pool}"
  IO.println s!"Total Mana: {pool.total}"
  IO.println ""

  IO.println "Can cast:"
  checkCard pool lightningBolt
  checkCard pool counterspell
  checkCard pool wrathOfGod
  checkCard pool llanowarElves
  checkCard pool blackLotus

  IO.println ""
  IO.println "Card Details:"
  for card in [lightningBolt, counterspell, wrathOfGod, llanowarElves, blackLotus] do
    IO.println s!"  {card.name}: {card.description}"
