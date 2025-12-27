/-!
# Basics of Lean 4

Fundamental concepts of Lean 4: numbers, functions, and code organization.
-/

namespace ZeroToQED.Basics

-- ANCHOR: from_zero
-- From Zero to QED: let's start at the very beginning
def zero : Nat := 0

#eval zero  -- Output: 0

-- The natural numbers are defined inductively:
-- Nat.zero is the base case
-- Nat.succ n is the successor of n
def one : Nat := Nat.succ Nat.zero
def two : Nat := Nat.succ (Nat.succ Nat.zero)

#eval one   -- Output: 1
#eval two   -- Output: 2

-- Of course, we can just write the literals directly
def fortyTwo : Nat := 42

-- The answer to life, the universe, and everything
theorem deep_thought : fortyTwo = 6 * 7 := rfl
-- ANCHOR_END: from_zero

-- ANCHOR: hello_world
def greet (name : String) : String :=
  s!"Hello, {name}!"

#eval greet "World"  -- Output: "Hello, World!"
-- ANCHOR_END: hello_world

-- ANCHOR: natural_numbers
-- Natural numbers (Nat) are non-negative integers: 0, 1, 2, 3, ...
def myNat : Nat := 42
def anotherNat : Nat := 100

-- Basic arithmetic
#eval 3 + 5      -- 8
#eval 10 - 3     -- 7 (truncated subtraction: 3 - 10 = 0)
#eval 4 * 7      -- 28
#eval 17 / 5     -- 3 (integer division)
#eval 17 % 5     -- 2 (modulo)

-- Natural number subtraction truncates at zero
#eval (3 : Nat) - 10  -- 0, not -7

-- Comparison
#eval 5 < 10     -- true
#eval 5 ≤ 5      -- true
#eval (10 == 10) -- true
-- ANCHOR_END: natural_numbers

-- ANCHOR: integers
-- Integers (Int) include negative numbers
def myInt : Int := -17
def posInt : Int := 42

-- Integer arithmetic handles negatives properly
#eval (-5 : Int) + 3     -- -2
#eval (3 : Int) - 10     -- -7
#eval (-4 : Int) * (-3)  -- 12
#eval (-17 : Int) / 5    -- -3
#eval (-17 : Int) % 5    -- -2

-- Converting between Nat and Int
#eval Int.ofNat 42             -- 42 as Int
#eval (42 : Int).toNat         -- 42 as Nat
#eval (-5 : Int).toNat         -- 0 (negative becomes 0)
#eval (42 : Int).natAbs        -- 42 (absolute value as Nat)
#eval (-42 : Int).natAbs       -- 42
-- ANCHOR_END: integers

-- ANCHOR: mathematical_curio
def taxicab : Nat := 1729

def isSumOfTwoCubes (n a b : Nat) : Bool :=
  a^3 + b^3 == n

#eval isSumOfTwoCubes taxicab 1 12   -- true: 1³ + 12³ = 1729
#eval isSumOfTwoCubes taxicab 9 10   -- true: 9³ + 10³ = 1729

def perfectNumbers : List Nat := [6, 28, 496, 8128]

def divisorSum (n : Nat) : Nat :=
  (List.range n).filter (fun d => d > 0 && n % d == 0) |>.foldl (· + ·) 0

#eval perfectNumbers.map divisorSum  -- [6, 28, 496, 8128]

def fibonacci : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibonacci n + fibonacci (n + 1)

#eval (List.range 12).map fibonacci  -- [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]
-- ANCHOR_END: mathematical_curio

-- ANCHOR: functions
def add (x : Nat) (y : Nat) : Nat :=
  x + y

def double : Nat → Nat :=
  fun x => 2 * x

def addFive := add 5  -- Partially applied function

#eval add 3 4        -- Output: 7
#eval double 21      -- Output: 42
#eval addFive 10     -- Output: 15
-- ANCHOR_END: functions

-- ANCHOR: pattern_matching
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def describe : Nat → String
  | 0 => "zero"
  | 1 => "one"
  | 2 => "two"
  | n => s!"many ({n})"

#eval factorial 5    -- Output: 120
#eval describe 0     -- Output: "zero"
#eval describe 100   -- Output: "many (100)"
-- ANCHOR_END: pattern_matching

-- ANCHOR: namespace_example
namespace Geometry2
  structure Point2 where
    x : Float
    y : Float

  def theOrigin : Point2 := ⟨0.0, 0.0⟩

  def dist (p q : Point2) : Float :=
    let dx := p.x - q.x
    let dy := p.y - q.y
    Float.sqrt (dx * dx + dy * dy)
end Geometry2

-- Access with full path
#eval Geometry2.dist Geometry2.theOrigin ⟨3.0, 4.0⟩  -- 5.0
-- ANCHOR_END: namespace_example

-- ANCHOR: open_example
-- Open brings namespace contents into scope
open Geometry2 in
#eval dist theOrigin ⟨3.0, 4.0⟩  -- 5.0

-- Open for a definition
open Geometry2 in
def unitCirclePoint (θ : Float) : Point2 := ⟨Float.cos θ, Float.sin θ⟩
-- ANCHOR_END: open_example

-- ANCHOR: section_variable
section VectorOps
  variable (α : Type) [Add α] [Mul α]

  -- α and the instances are automatically added as implicit parameters
  def doubleIt (x : α) : α := x + x
  def squareIt (x : α) : α := x * x
end VectorOps

#eval doubleIt Nat 21    -- 42
#eval squareIt Nat 7     -- 49
-- ANCHOR_END: section_variable

-- ANCHOR: visibility
namespace Internal
  private def helperVal : Nat := 42

  def publicApi : Nat := helperVal * 2
end Internal

#eval Internal.publicApi          -- 84
-- helperVal is not accessible outside this file
-- ANCHOR_END: visibility

-- ANCHOR: export_example
namespace Math
  def square (x : Nat) : Nat := x * x
  def cube (x : Nat) : Nat := x * x * x
end Math

namespace Prelude
  -- Re-export square from Math into Prelude
  export Math (square)
end Prelude

-- Now square is available via Prelude without opening Math
#eval Prelude.square 5  -- 25
-- ANCHOR_END: export_example

-- ANCHOR: lemma_example
-- lemma is identical to theorem (historical terminology from mathematics)
theorem zero_add_self (n : Nat) : 0 + n = n := Nat.zero_add n
-- The `lemma` keyword is an alias for `theorem`
-- ANCHOR_END: lemma_example

-- ANCHOR: abbrev_example
-- abbrev creates a transparent abbreviation (always unfolded)
abbrev NatPair := Nat × Nat
abbrev Predicate' (α : Type) := α → Bool

def isEvenPred : Predicate' Nat := fun n => n % 2 == 0
def sumPair (p : NatPair) : Nat := p.1 + p.2

#eval isEvenPred 4       -- true
#eval sumPair (3, 7)     -- 10
-- ANCHOR_END: abbrev_example

-- ANCHOR: opaque_example
-- opaque hides the implementation (never unfolds)
opaque secretKey : Nat

-- The type checker cannot see any value for secretKey
-- This is useful for abstraction barriers
-- ANCHOR_END: opaque_example

-- ANCHOR: axiom_example
-- axiom asserts something without proof
-- WARNING: Incorrect axioms make the entire system inconsistent!
axiom magicNumber : Nat
axiom magicNumber_positive : magicNumber > 0

-- Use axioms only for:
-- 1. Foundational assumptions (excluded middle, choice)
-- 2. FFI bindings where proofs are impossible
-- 3. Temporary placeholders during development (prefer sorry)
-- ANCHOR_END: axiom_example

-- ANCHOR: attribute_example
-- Attributes attach metadata to declarations
@[simp] theorem add_zero_right' (n : Nat) : n + 0 = n := Nat.add_zero n

-- The @[simp] attribute marks this for use by the simp tactic
-- Common attributes: simp, inline, reducible, instance, class
-- ANCHOR_END: attribute_example

-- ANCHOR: check_print_reduce
-- #check shows the type of an expression
#check (fun x : Nat => x + 1)  -- Nat → Nat
#check @List.map              -- shows full polymorphic type

-- #print shows information about a declaration
#print Nat.add
#print List

-- #reduce reduces an expression to normal form
#reduce (fun x => x + 1) 5    -- 6
#reduce List.map (· + 1) [1, 2, 3]  -- [2, 3, 4]
-- ANCHOR_END: check_print_reduce

-- ANCHOR: universe_example
-- Universe declarations specify type levels
universe u v

-- Now u and v can be used in type signatures
def myId.{w} (α : Type w) (x : α) : α := x

-- Types themselves have types: Type 0 : Type 1 : Type 2 : ...
#check (Nat : Type 0)
#check (Type 0 : Type 1)
#check (Type 1 : Type 2)
-- ANCHOR_END: universe_example

-- ANCHOR: notation_example
-- Custom notation for domain-specific syntax
notation "⟪" a ", " b "⟫" => (a, b)

#eval ⟪1, 2⟫  -- (1, 2)

-- Prefix notation
prefix:max "∼" => fun (n : Nat) => n + 1

#eval ∼5  -- 6
-- ANCHOR_END: notation_example

-- ANCHOR: set_option_example
-- set_option configures compiler and elaborator behavior
set_option pp.explicit true in
#check @id Nat 5  -- shows implicit arguments

set_option maxRecDepth 1000 in
def deepRecursion (n : Nat) : Nat :=
  if n = 0 then 0 else deepRecursion (n - 1)
-- ANCHOR_END: set_option_example

end ZeroToQED.Basics
