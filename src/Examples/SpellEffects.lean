-- Spell Effects with Type Classes
-- Run with: lake exe spells

-- ANCHOR: elements
inductive Element where
  | fire | ice | lightning | holy | dark
  deriving Repr, DecidableEq

def Element.name : Element → String
  | .fire => "fire"
  | .ice => "ice"
  | .lightning => "lightning"
  | .holy => "holy"
  | .dark => "dark"
-- ANCHOR_END: elements

-- ANCHOR: effect_types
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
-- ANCHOR_END: effect_types

-- ANCHOR: spell_effect_class
class SpellEffect (ε : Type) where
  describe : ε → String
  potency : ε → Nat

instance : SpellEffect Damage where
  describe d := s!"{d.amount} {d.element.name} damage"
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
-- ANCHOR_END: spell_effect_class

-- ANCHOR: compound_effects
inductive Effect where
  | damage (d : Damage)
  | healing (h : Healing)
  | buff (b : Buff)
  | status (s : StatusEffect)
  | compound (fst snd : Effect)
  deriving Repr

def Effect.describe : Effect → String
  | .damage d => SpellEffect.describe d
  | .healing h => SpellEffect.describe h
  | .buff b => SpellEffect.describe b
  | .status s => SpellEffect.describe s
  | .compound fst snd => s!"{fst.describe} + {snd.describe}"

def Effect.potency : Effect → Nat
  | .damage d => SpellEffect.potency d
  | .healing h => SpellEffect.potency h
  | .buff b => SpellEffect.potency b
  | .status s => SpellEffect.potency s
  | .compound fst snd => fst.potency + snd.potency

instance : SpellEffect Effect where
  describe := Effect.describe
  potency := Effect.potency

instance : Append Effect where
  append := Effect.compound
-- ANCHOR_END: compound_effects

-- ANCHOR: spell_casting
structure Spell (ε : Type) where
  name : String
  manaCost : Nat
  effect : ε

def castSpell {ε : Type} [SpellEffect ε] (s : Spell ε) : String :=
  let desc := SpellEffect.describe s.effect
  let pot := SpellEffect.potency s.effect
  s!"{s.name} (Cost: {s.manaCost} MP): {desc} [Potency: {pot}]"
-- ANCHOR_END: spell_casting

-- ANCHOR: simple_spells
def fireball : Spell Damage := ⟨"Fireball", 3, ⟨8, .fire⟩⟩
def frostbolt : Spell Damage := ⟨"Frostbolt", 2, ⟨5, .ice⟩⟩
def heal : Spell Healing := ⟨"Heal", 4, ⟨20⟩⟩
def haste : Spell Buff := ⟨"Haste", 3, ⟨"Speed", 2, 5⟩⟩
-- ANCHOR_END: simple_spells

-- ANCHOR: compound_spells
def drainLife : Spell Effect :=
  ⟨"Drain Life", 4,
    .damage ⟨6, .dark⟩ ++ .healing ⟨6⟩⟩

def chaosStorm : Spell Effect :=
  ⟨"Chaos Storm", 8,
    .damage ⟨5, .fire⟩ ++ .damage ⟨5, .ice⟩ ++ .damage ⟨5, .lightning⟩⟩

def holyWrath : Spell Effect :=
  ⟨"Holy Wrath", 6,
    .damage ⟨10, .holy⟩ ++ .buff ⟨"Defense", 3, 3⟩⟩

def venomStrike : Spell Effect :=
  ⟨"Venom Strike", 3,
    .damage ⟨4, .dark⟩ ++ .status ⟨"Poisoned", 4⟩⟩

def battleHymn : Spell Effect :=
  ⟨"Battle Hymn", 5,
    .buff ⟨"Strength", 2, 4⟩ ++ .buff ⟨"Speed", 1, 4⟩ ++ .healing ⟨8⟩⟩
-- ANCHOR_END: compound_spells

def main : IO Unit := do
  IO.println "=== Spell Effects Demo ===\n"

  IO.println "--- Simple Spells ---"
  IO.println (castSpell fireball)
  IO.println (castSpell frostbolt)
  IO.println (castSpell heal)
  IO.println (castSpell haste)
  IO.println ""

  IO.println "--- Compound Spells ---"
  IO.println (castSpell drainLife)
  IO.println (castSpell chaosStorm)
  IO.println (castSpell holyWrath)
  IO.println (castSpell venomStrike)
  IO.println (castSpell battleHymn)
