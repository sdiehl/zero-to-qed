/-
Dependent Types Examples

Examples demonstrating dependent types, Fin, Vector, and dependent pattern matching.
-/

import Mathlib.Tactic

namespace ZeroToQED.DependentTypes

-- ANCHOR: fin_basics
-- Fin n: natural numbers less than n

-- Fin 3 has exactly three values: 0, 1, 2
example : Fin 3 := 0
example : Fin 3 := 1
example : Fin 3 := 2
-- example : Fin 3 := 3  -- Error: 3 is not less than 3

-- Fin carries a proof that the value is in bounds
def two : Fin 5 := ⟨2, by omega⟩

-- Safe array indexing using Fin
def safeIndex {α : Type} (arr : Array α) (i : Fin arr.size) : α :=
  arr[i]  -- No bounds check needed at runtime
-- ANCHOR_END: fin_basics

-- ANCHOR: vector_type
-- Vector: lists with length in the type

-- A vector is a list with its length tracked in the type
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

-- The length is known at compile time
def exampleVec : Vec Nat 3 := .cons 1 (.cons 2 (.cons 3 .nil))

-- Head is safe: can only call on non-empty vectors
def Vec.head {α : Type} {n : Nat} : Vec α (n + 1) → α
  | .cons x _ => x

-- Tail preserves the length relationship
def Vec.tail {α : Type} {n : Nat} : Vec α (n + 1) → Vec α n
  | .cons _ xs => xs

-- Map over a vector (preserves length)
def Vec.map {α β : Type} {n : Nat} (f : α → β) : Vec α n → Vec β n
  | .nil => .nil
  | .cons x xs => .cons (f x) (xs.map f)
-- ANCHOR_END: vector_type

-- ANCHOR: dependent_return_type
-- Return type depends on runtime value - impossible in Haskell/OCaml
def dependentTwo (b : Bool) : if b then Unit × Unit else String :=
  match b with
  | true => ((), ())    -- Returns a pair when b is true
  | false => "two"      -- Returns a string when b is false
-- ANCHOR_END: dependent_return_type

-- ANCHOR: dependent_pattern_matching
-- Dependent pattern matching: types change based on scrutinee

-- Return type depends on the boolean value
def boolToType (b : Bool) : Type :=
  if b then Nat else String

def boolExample (b : Bool) : boolToType b :=
  match b with
  | true => (42 : Nat)  -- returns Nat
  | false => "hello"    -- returns String

-- Pattern matching on Fin must handle all cases
def finToString : Fin 3 → String
  | 0 => "zero"
  | 1 => "one"
  | 2 => "two"
-- ANCHOR_END: dependent_pattern_matching

-- ANCHOR: sigma_types
-- Sigma types: dependent pairs

-- A dependent pair where the second type depends on the first value
-- Σ (n : Nat), Fin n  means "a natural number n paired with a Fin n"
def dependentPair : Σ n : Nat, Fin n := ⟨5, 3⟩

-- The second component's type depends on the first
example : dependentPair.fst = 5 := rfl
example : dependentPair.snd < dependentPair.fst := by decide

-- Contrast with non-dependent product
def regularPair : Nat × Nat := (5, 3)  -- both components are Nat
-- ANCHOR_END: sigma_types

-- ANCHOR: subtype
-- Subtypes: values with proofs

-- { x : Nat // x > 0 } is the type of positive naturals
def posNat : { n : Nat // n > 0 } := ⟨5, by omega⟩

-- Access the value and proof separately
example : posNat.val = 5 := rfl
example : posNat.property = (by omega : 5 > 0) := rfl

-- Functions can require positive inputs
def safeDivide (a : Nat) (b : { n : Nat // n > 0 }) : Nat :=
  a / b.val
-- ANCHOR_END: subtype

-- ANCHOR: equality_types
-- Equality as a dependent type

-- The equality type: a = b is a type that is inhabited iff a equals b
-- rfl : a = a is the only constructor
example : 2 + 2 = 4 := rfl

-- Proofs of equality can be used to substitute
theorem subst_example (a b : Nat) (h : a = b) (P : Nat → Prop) (pa : P a) : P b :=
  h ▸ pa  -- transport pa along h

-- Equality is symmetric and transitive
theorem eq_symm (a b : Nat) (h : a = b) : b = a := h.symm
theorem eq_trans (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := h1.trans h2
-- ANCHOR_END: equality_types

-- ANCHOR: termination
-- Termination proofs for recursive functions

-- Lean requires proof that recursion terminates
-- For structural recursion, it's automatic
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- For non-structural recursion, provide a termination measure
def gcd (a b : Nat) : Nat :=
  if h : b = 0 then a
  else
    have : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero h)
    gcd b (a % b)
termination_by b

-- The measure must decrease on each recursive call
def ackermann : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ackermann m 1
  | m + 1, n + 1 => ackermann m (ackermann (m + 1) n)
termination_by m n => (m, n)
-- ANCHOR_END: termination

-- ANCHOR: universe_polymorphism
-- Universe polymorphism

-- Types live in universes: Type 0, Type 1, Type 2, ...
-- Type : Type would lead to paradoxes (Russell, Girard)

-- Universe-polymorphic identity function
universe u
def id' {α : Type u} (x : α) : α := x

-- Works at any universe level
example : id' 42 = 42 := rfl           -- Type 0
example : id' Nat = Nat := rfl         -- Type 1
example : id' (Type 0) = Type 0 := rfl -- Type 2
-- ANCHOR_END: universe_polymorphism

end ZeroToQED.DependentTypes
