-- Spell Effects with Type Classes
-- Run with: lake exe spells

-- ANCHOR: spell_effects
inductive Element where
  | fire | ice | lightning | holy | dark
  deriving Repr, DecidableEq

structure Damage where
  amount : Nat
  element : Element
  deriving Repr

structure Healing where
  amount : Nat
  deriving Repr

structure Buff where
  stat : String
  bonus : Int
  duration : Nat
  deriving Repr

structure StatusEffect where
  name : String
  duration : Nat
  deriving Repr

class SpellEffect (ε : Type) where
  describe : ε → String
  potency : ε → Nat

instance : SpellEffect Damage where
  describe d :=
    let elem := match d.element with
      | .fire => "fire"
      | .ice => "ice"
      | .lightning => "lightning"
      | .holy => "holy"
      | .dark => "dark"
    s!"{d.amount} {elem} damage"
  potency d := d.amount

instance : SpellEffect Healing where
  describe h := s!"restore {h.amount} HP"
  potency h := h.amount

instance : SpellEffect Buff where
  describe b := s!"+{b.bonus} {b.stat} for {b.duration} turns"
  potency b := b.bonus.natAbs * b.duration

instance : SpellEffect StatusEffect where
  describe s := s!"{s.name} for {s.duration} turns"
  potency s := s.duration * 2

structure Spell (ε : Type) where
  name : String
  manaCost : Nat
  effect : ε

def castSpell {ε : Type} [SpellEffect ε] (s : Spell ε) : String :=
  let desc := SpellEffect.describe s.effect
  let pot := SpellEffect.potency s.effect
  s!"{s.name} (Cost: {s.manaCost} MP): {desc} [Potency: {pot}]"

-- Damage spells
def fireball : Spell Damage := ⟨"Fireball", 3, ⟨8, .fire⟩⟩
-- ANCHOR_END: spell_effects

def iceStorm : Spell Damage := ⟨"Ice Storm", 4, ⟨6, .ice⟩⟩
def lightningBolt : Spell Damage := ⟨"Lightning Bolt", 2, ⟨5, .lightning⟩⟩
def holySmite : Spell Damage := ⟨"Holy Smite", 5, ⟨12, .holy⟩⟩
def shadowBolt : Spell Damage := ⟨"Shadow Bolt", 3, ⟨7, .dark⟩⟩

-- Healing spells
def cureLightWounds : Spell Healing := ⟨"Cure Light Wounds", 1, ⟨6⟩⟩
def heal : Spell Healing := ⟨"Heal", 4, ⟨20⟩⟩
def regenerate : Spell Healing := ⟨"Regenerate", 6, ⟨35⟩⟩

-- Buff spells
def haste : Spell Buff := ⟨"Haste", 3, ⟨"Speed", 2, 5⟩⟩
def giantStrength : Spell Buff := ⟨"Giant Strength", 2, ⟨"Strength", 4, 3⟩⟩
def stoneskin : Spell Buff := ⟨"Stoneskin", 4, ⟨"Defense", 5, 4⟩⟩

-- Status effects
def sleep : Spell StatusEffect := ⟨"Sleep", 2, ⟨"Asleep", 3⟩⟩
def poison : Spell StatusEffect := ⟨"Poison", 1, ⟨"Poisoned", 5⟩⟩
def blind : Spell StatusEffect := ⟨"Blind", 2, ⟨"Blinded", 2⟩⟩

def main : IO Unit := do
  IO.println "=== Spell Effects Demo ==="
  IO.println ""

  IO.println "--- Damage Spells ---"
  IO.println (castSpell fireball)
  IO.println (castSpell iceStorm)
  IO.println (castSpell lightningBolt)
  IO.println (castSpell holySmite)
  IO.println (castSpell shadowBolt)
  IO.println ""

  IO.println "--- Healing Spells ---"
  IO.println (castSpell cureLightWounds)
  IO.println (castSpell heal)
  IO.println (castSpell regenerate)
  IO.println ""

  IO.println "--- Buff Spells ---"
  IO.println (castSpell haste)
  IO.println (castSpell giantStrength)
  IO.println (castSpell stoneskin)
  IO.println ""

  IO.println "--- Status Effects ---"
  IO.println (castSpell sleep)
  IO.println (castSpell poison)
  IO.println (castSpell blind)
