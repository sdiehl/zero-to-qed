-- Magic: The Gathering Card System
-- Run with: lake exe mtg

-- ANCHOR: mana_colors
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

def ManaCost.total (c : ManaCost) : Nat :=
  c.white + c.blue + c.black + c.red + c.green + c.colorless
-- ANCHOR_END: mana_colors

-- ANCHOR: mana_pool
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

def ManaPool.canAfford (pool : ManaPool) (cost : ManaCost) : Bool :=
  pool.white >= cost.white &&
  pool.blue >= cost.blue &&
  pool.black >= cost.black &&
  pool.red >= cost.red &&
  pool.green >= cost.green &&
  pool.total >= cost.total

def ManaPool.pay (pool : ManaPool) (cost : ManaCost) : Option ManaPool :=
  if pool.canAfford cost then
    some { white := pool.white - cost.white
           blue := pool.blue - cost.blue
           black := pool.black - cost.black
           red := pool.red - cost.red
           green := pool.green - cost.green
           colorless := pool.total - cost.total -
             (pool.white - cost.white) - (pool.blue - cost.blue) -
             (pool.black - cost.black) - (pool.red - cost.red) -
             (pool.green - cost.green) }
  else
    none
-- ANCHOR_END: mana_pool

-- ANCHOR: card_types
inductive CardType where
  | creature (power : Nat) (toughness : Nat)
  | instant
  | sorcery
  | enchantment
  | artifact
  deriving Repr

structure Card where
  name : String
  cost : ManaCost
  cardType : CardType
  deriving Repr
-- ANCHOR_END: card_types

-- ANCHOR: sample_cards
def goblinGuide : Card :=
  { name := "Goblin Guide"
    cost := { red := 1 }
    cardType := .creature 2 2 }

def searingSpear : Card :=
  { name := "Searing Spear"
    cost := { red := 1, colorless := 1 }
    cardType := .instant }

def dayOfJudgment : Card :=
  { name := "Day of Judgment"
    cost := { white := 2, colorless := 2 }
    cardType := .sorcery }

def swordOfFire : Card :=
  { name := "Sword of Fire and Ice"
    cost := { colorless := 3 }
    cardType := .artifact }

def graveTitan : Card :=
  { name := "Grave Titan"
    cost := { black := 2, colorless := 4 }
    cardType := .creature 6 6 }
-- ANCHOR_END: sample_cards

-- ANCHOR: card_queries
def Card.isCreature (c : Card) : Bool :=
  match c.cardType with
  | .creature _ _ => true
  | _ => false

def Card.power (c : Card) : Option Nat :=
  match c.cardType with
  | .creature p _ => some p
  | _ => none

def Card.toughness (c : Card) : Option Nat :=
  match c.cardType with
  | .creature _ t => some t
  | _ => none
-- ANCHOR_END: card_queries

-- ANCHOR: combat
structure Creature where
  name : String
  power : Nat
  toughness : Nat
  damage : Nat := 0
  deriving Repr

def Creature.fromCard (c : Card) : Option Creature :=
  match c.cardType with
  | .creature p t => some { name := c.name, power := p, toughness := t }
  | _ => none

def Creature.isAlive (c : Creature) : Bool :=
  c.damage < c.toughness

def Creature.takeDamage (c : Creature) (dmg : Nat) : Creature :=
  { c with damage := c.damage + dmg }

def Creature.canBlock (blocker attacker : Creature) : Bool :=
  blocker.isAlive && attacker.isAlive

def combat (attacker blocker : Creature) : Creature × Creature :=
  let attackerAfter := attacker.takeDamage blocker.power
  let blockerAfter := blocker.takeDamage attacker.power
  (attackerAfter, blockerAfter)
-- ANCHOR_END: combat

-- ANCHOR: hand
abbrev Hand := List Card

def Hand.playable (hand : Hand) (pool : ManaPool) : List Card :=
  hand.filter (fun c => pool.canAfford c.cost)

def Hand.creatures (hand : Hand) : List Card :=
  hand.filter Card.isCreature

def Hand.totalCost (hand : Hand) : Nat :=
  hand.foldl (fun acc c => acc + c.cost.total) 0
-- ANCHOR_END: hand

-- Formatting helpers for output
def formatCost (c : ManaCost) : String :=
  let parts := #[
    if c.colorless > 0 then s!"{c.colorless}" else "",
    String.ofList (List.replicate c.white 'W'),
    String.ofList (List.replicate c.blue 'U'),
    String.ofList (List.replicate c.black 'B'),
    String.ofList (List.replicate c.red 'R'),
    String.ofList (List.replicate c.green 'G')
  ]
  let result := String.join (parts.toList.filter (· ≠ ""))
  if result.isEmpty then "0" else result

def formatCard (c : Card) : String :=
  let typeStr := match c.cardType with
    | .creature p t => s!"Creature {p}/{t}"
    | .instant => "Instant"
    | .sorcery => "Sorcery"
    | .enchantment => "Enchantment"
    | .artifact => "Artifact"
  s!"{c.name} ({formatCost c.cost}) - {typeStr}"

def formatCreature (c : Creature) : String :=
  let status := if c.isAlive then "alive" else "dead"
  s!"{c.name} {c.power}/{c.toughness} ({c.damage} damage, {status})"

def main : IO Unit := do
  IO.println "=== Magic: The Gathering Card System ===\n"

  -- Mana pool
  let pool : ManaPool := { red := 2, black := 3, colorless := 1 }
  IO.println s!"Mana available: {pool.total} total"

  -- Hand of cards
  let hand : Hand := [goblinGuide, searingSpear, dayOfJudgment, graveTitan, swordOfFire]
  IO.println s!"\nHand ({hand.length} cards):"
  for card in hand do
    let castable := if pool.canAfford card.cost then "✓" else "✗"
    IO.println s!"  {castable} {formatCard card}"

  -- Playable cards
  let playable := hand.playable pool
  IO.println s!"\nPlayable cards: {playable.length}"

  -- Creatures in hand
  let creatures := hand.creatures
  IO.println s!"Creatures in hand: {creatures.length}"

  -- Combat example
  IO.println "\n=== Combat Example ==="
  let attacker : Creature := { name := "Goblin Guide", power := 2, toughness := 2 }
  let blocker : Creature := { name := "Grizzly Bears", power := 2, toughness := 2 }

  IO.println s!"Attacker: {formatCreature attacker}"
  IO.println s!"Blocker:  {formatCreature blocker}"

  let (attackerAfter, blockerAfter) := combat attacker blocker
  IO.println "\nAfter combat:"
  IO.println s!"Attacker: {formatCreature attackerAfter}"
  IO.println s!"Blocker:  {formatCreature blockerAfter}"
