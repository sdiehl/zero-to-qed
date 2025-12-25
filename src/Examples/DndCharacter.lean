-- D&D Character Generator
-- Run with: lake exe dnd [seed]

structure AbilityScores where
  strength : Nat
  dexterity : Nat
  constitution : Nat
  intelligence : Nat
  wisdom : Nat
  charisma : Nat
  deriving Repr

inductive Race where
  | human
  | elf
  | dwarf
  | halfling
  | dragonborn
  | tiefling
  deriving Repr, DecidableEq

inductive CharClass where
  | fighter   -- d10 hit die
  | wizard    -- d6 hit die
  | rogue     -- d8 hit die
  | cleric    -- d8 hit die
  | barbarian -- d12 hit die
  | bard      -- d8 hit die
  deriving Repr, DecidableEq

inductive Background where
  | soldier
  | sage
  | criminal
  | noble
  | hermit
  | entertainer
  deriving Repr, DecidableEq

structure Character where
  name : String
  race : Race
  charClass : CharClass
  background : Background
  level : Nat
  abilities : AbilityScores
  hitPoints : Nat
  deriving Repr

def racialBonuses (r : Race) : AbilityScores :=
  match r with
  | .human      => { strength := 1, dexterity := 1, constitution := 1,
                     intelligence := 1, wisdom := 1, charisma := 1 }
  | .elf        => { strength := 0, dexterity := 2, constitution := 0,
                     intelligence := 1, wisdom := 0, charisma := 0 }
  | .dwarf      => { strength := 0, dexterity := 0, constitution := 2,
                     intelligence := 0, wisdom := 1, charisma := 0 }
  | .halfling   => { strength := 0, dexterity := 2, constitution := 0,
                     intelligence := 0, wisdom := 0, charisma := 1 }
  | .dragonborn => { strength := 2, dexterity := 0, constitution := 0,
                     intelligence := 0, wisdom := 0, charisma := 1 }
  | .tiefling   => { strength := 0, dexterity := 0, constitution := 0,
                     intelligence := 1, wisdom := 0, charisma := 2 }

def hitDie (c : CharClass) : Nat :=
  match c with
  | .wizard    => 6
  | .rogue     => 8
  | .bard      => 8
  | .cleric    => 8
  | .fighter   => 10
  | .barbarian => 12

structure RNG where
  state : Nat
  deriving Repr

def RNG.next (rng : RNG) : RNG × Nat :=
  let newState := (rng.state * 1103515245 + 12345) % (2^31)
  (⟨newState⟩, newState)

def RNG.range (rng : RNG) (lo hi : Nat) : RNG × Nat :=
  let (rng', n) := rng.next
  let range := hi - lo + 1
  (rng', lo + n % range)

def roll4d6DropLowest (rng : RNG) : RNG × Nat :=
  let (rng1, d1) := rng.range 1 6
  let (rng2, d2) := rng1.range 1 6
  let (rng3, d3) := rng2.range 1 6
  let (rng4, d4) := rng3.range 1 6
  let dice := [d1, d2, d3, d4]
  let sorted := dice.toArray.qsort (· < ·) |>.toList
  let top3 := sorted.drop 1
  (rng4, top3.foldl (· + ·) 0)

def rollAbilityScores (rng : RNG) : RNG × AbilityScores :=
  let (rng1, str) := roll4d6DropLowest rng
  let (rng2, dex) := roll4d6DropLowest rng1
  let (rng3, con) := roll4d6DropLowest rng2
  let (rng4, int) := roll4d6DropLowest rng3
  let (rng5, wis) := roll4d6DropLowest rng4
  let (rng6, cha) := roll4d6DropLowest rng5
  (rng6, { strength := str, dexterity := dex, constitution := con,
           intelligence := int, wisdom := wis, charisma := cha })

def applyRacialBonuses (base : AbilityScores) (race : Race) : AbilityScores :=
  let bonus := racialBonuses race
  { strength := base.strength + bonus.strength
    dexterity := base.dexterity + bonus.dexterity
    constitution := base.constitution + bonus.constitution
    intelligence := base.intelligence + bonus.intelligence
    wisdom := base.wisdom + bonus.wisdom
    charisma := base.charisma + bonus.charisma }

def abilityModifier (score : Nat) : Int :=
  (score : Int) / 2 - 5

def startingHP (con : Nat) (c : CharClass) : Nat :=
  let conMod := abilityModifier con
  let baseHP := hitDie c
  if conMod < 0 && baseHP < conMod.natAbs then 1
  else (baseHP : Int) + conMod |>.toNat

def pickRandom {α : Type} (rng : RNG) (xs : List α) (default : α) : RNG × α :=
  match xs with
  | [] => (rng, default)
  | _ =>
    let (rng', idx) := rng.range 0 (xs.length - 1)
    (rng', xs[idx]?.getD default)

def allRaces : List Race := [.human, .elf, .dwarf, .halfling, .dragonborn, .tiefling]
def allClasses : List CharClass := [.fighter, .wizard, .rogue, .cleric, .barbarian, .bard]
def allBackgrounds : List Background := [.soldier, .sage, .criminal, .noble, .hermit, .entertainer]

def fantasyNames : List String := [
  "Thorin", "Elara", "Grimjaw", "Pip", "Aethon", "Cornelius"
]

def generateCharacter (seed : Nat) : Character :=
  let rng : RNG := ⟨seed⟩
  let (rng1, name) := pickRandom rng fantasyNames "Adventurer"
  let (rng2, race) := pickRandom rng1 allRaces .human
  let (rng3, charClass) := pickRandom rng2 allClasses .fighter
  let (rng4, background) := pickRandom rng3 allBackgrounds .soldier
  let (_, baseAbilities) := rollAbilityScores rng4
  let abilities := applyRacialBonuses baseAbilities race
  let hp := startingHP abilities.constitution charClass
  { name := name
    race := race
    charClass := charClass
    background := background
    level := 1
    abilities := abilities
    hitPoints := hp }

def raceName : Race → String
  | .human => "Human"
  | .elf => "Elf"
  | .dwarf => "Dwarf"
  | .halfling => "Halfling"
  | .dragonborn => "Dragonborn"
  | .tiefling => "Tiefling"

def className : CharClass → String
  | .fighter => "Fighter"
  | .wizard => "Wizard"
  | .rogue => "Rogue"
  | .cleric => "Cleric"
  | .barbarian => "Barbarian"
  | .bard => "Bard"

def backgroundName : Background → String
  | .soldier => "Soldier"
  | .sage => "Sage"
  | .criminal => "Criminal"
  | .noble => "Noble"
  | .hermit => "Hermit"
  | .entertainer => "Entertainer"

def formatModifier (score : Nat) : String :=
  let m := abilityModifier score
  if m >= 0 then s!"+{m}" else s!"{m}"

def printCharacter (c : Character) : IO Unit := do
  IO.println "======================================"
  IO.println s!"  {c.name}"
  IO.println "======================================"
  IO.println s!"  Level {c.level} {raceName c.race} {className c.charClass}"
  IO.println s!"  Background: {backgroundName c.background}"
  IO.println ""
  IO.println "  ABILITY SCORES"
  IO.println "  --------------"
  IO.println s!"  STR: {c.abilities.strength} ({formatModifier c.abilities.strength})"
  IO.println s!"  DEX: {c.abilities.dexterity} ({formatModifier c.abilities.dexterity})"
  IO.println s!"  CON: {c.abilities.constitution} ({formatModifier c.abilities.constitution})"
  IO.println s!"  INT: {c.abilities.intelligence} ({formatModifier c.abilities.intelligence})"
  IO.println s!"  WIS: {c.abilities.wisdom} ({formatModifier c.abilities.wisdom})"
  IO.println s!"  CHA: {c.abilities.charisma} ({formatModifier c.abilities.charisma})"
  IO.println ""
  IO.println s!"  Hit Points: {c.hitPoints}"
  IO.println s!"  Hit Die: d{hitDie c.charClass}"
  IO.println "======================================"

def main (args : List String) : IO Unit := do
  let seed := match args.head? >>= String.toNat? with
    | some n => n
    | none => 42

  IO.println ""
  IO.println "  D&D CHARACTER GENERATOR"
  IO.println "  Type-Safe Adventures Await!"
  IO.println ""

  let character := generateCharacter seed

  printCharacter character

  IO.println ""
  IO.println "Your adventure begins..."
  IO.println "(Use a different seed for a different character: lake exe dnd <seed>)"
