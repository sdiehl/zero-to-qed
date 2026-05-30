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
#eval 3 - 10  -- 0, not -7

-- Comparison returns Bool
#eval 5 < 10     -- true
#eval 5 ≤ 5      -- true
#eval 10 == 10   -- true
-- ANCHOR_END: natural_numbers

-- ANCHOR: integers
-- Integers (Int) include negative numbers
def myInt : Int := -17
def posInt : Int := 42

-- Integer arithmetic handles negatives properly
-- Starting with a negative infers Int automatically
#eval -5 + 3     -- -2
#eval -4 * -3    -- 12
#eval -17 / 5    -- -3
#eval -17 % 5    -- -2
-- But positive minus larger needs annotation
#eval (3 : Int) - 10     -- -7

-- Converting between Nat and Int
#eval Int.ofNat 42             -- 42 as Int
#eval (42 : Int).toNat         -- 42 as Nat
#eval (-5 : Int).toNat         -- 0 (negative becomes 0)
#eval (42 : Int).natAbs        -- 42 (absolute value as Nat)
#eval (-42 : Int).natAbs       -- 42
-- ANCHOR_END: integers

-- ANCHOR: comments
-- Single-line comments start with double dash
-- Everything after -- is ignored until end of line

/- Block comments are delimited by /- and -/
   They can span multiple lines
   and are useful for temporarily disabling code -/

/-- Documentation comments start with /-- and end with -/
    They attach to the following declaration and support markdown.
    Use these to document your API. -/
def documented (n : Nat) : Nat := n + 1

/-! Module-level documentation uses /-! and -/
    Place these at the top of a file to describe the module's purpose.
    Documentation tools extract these comments automatically. -/

-- Comments nest properly:
/- outer /- inner -/ still outer -/

-- The #check command is not affected by comments on the same line
#check Nat  -- this comment doesn't interfere
-- ANCHOR_END: comments

-- ANCHOR: composition
def twice (n : Nat) := n * 2
def square (n : Nat) := n * n
def inc (n : Nat) := n + 1

-- ∘ composes right-to-left: (f ∘ g) x = f (g x)
#eval (square ∘ twice) 3           -- 36: square(twice(3)) = square(6)
#eval (twice ∘ square) 3           -- 18: twice(square(3)) = twice(9)
#eval (inc ∘ square ∘ twice) 3     -- 37: inc(square(twice(3))) = inc(square(6))

-- |> pipes left-to-right: x |> f |> g = g (f x)
#eval 3 |> twice |> square |> inc  -- 37: same computation, opposite order
#eval 10 |> twice                  -- 20
#eval [1, 2, 3] |> List.reverse    -- [3, 2, 1]

-- <| is low-precedence application: f <| x = f x
-- useful to avoid parentheses
#eval String.length <| "hello" ++ " world"  -- 11
#eval List.map twice <| [1, 2, 3]           -- [2, 4, 6]

-- chaining with methods vs pipes
#eval [1, 2, 3].map twice |> List.reverse        -- [6, 4, 2]
#eval ([1, 2, 3].map twice).reverse              -- same

-- composition builds new functions without naming arguments
def processThenSquare := square ∘ twice ∘ inc
#eval processThenSquare 2                        -- 36: square(twice(inc(2)))
-- ANCHOR_END: composition

-- ANCHOR: fp_essentials
-- Higher-order functions
#eval [1, 2, 3, 4, 5].map (· * 2)         -- [2, 4, 6, 8, 10]
#eval [1, 2, 3, 4, 5].filter (· > 2)      -- [3, 4, 5]
#eval [1, 2, 3, 4, 5].foldl (· + ·) 100   -- 115 (100 + 1 + 2 + 3 + 4 + 5)

-- Programs are proofs: addition is commutative
theorem add_comm_example : 2 + 3 = 3 + 2 := rfl

-- Computation IS proof: complex operations verified by evaluation
example : [1, 2, 3].reverse.reverse = [1, 2, 3] := rfl
example : [1, 2, 3].length + [4, 5].length = 5 := rfl
example : [1, 2, 3].map (· + 10) = [11, 12, 13] := rfl
-- ANCHOR_END: fp_essentials

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

open Geometry2
-- ANCHOR: angle_brackets
def explicit : Point2 := Point2.mk 3.0 4.0
def shorthand : Point2 := ⟨3.0, 4.0⟩
-- ANCHOR_END: angle_brackets

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

-- ANCHOR: scoping
-- let bindings create local scope within an expression
def hypotenuse (a b : Float) : Float :=
  let aSquared := a * a
  let bSquared := b * b
  Float.sqrt (aSquared + bSquared)
  -- aSquared and bSquared are not visible outside this def

-- where clauses provide the same scoping, but definitions come after use
def quadraticRoots (a b c : Float) : Float × Float :=
  ((-b + discriminant) / denom, (-b - discriminant) / denom)
where
  discriminant := Float.sqrt (b * b - 4 * a * c)
  denom := 2 * a

-- Scopes nest: inner let shadows outer
def shadowExample : Nat :=
  let x := 1
  let result :=
    let x := 2      -- shadows outer x
    x + 10          -- uses inner x: 12
  result + x        -- uses outer x: 12 + 1 = 13

#eval shadowExample  -- 13
-- ANCHOR_END: scoping

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
-- Types themselves have types, forming a hierarchy
#check (Nat : Type 0)      -- Nat lives in Type 0
#check (Type 0 : Type 1)   -- Type 0 lives in Type 1
#check (Type 1 : Type 2)   -- and so on...

-- Universe variables let definitions work at any level
-- The .{u} syntax declares a universe parameter for this definition
def myId.{u} (α : Type u) (x : α) : α := x

-- myId works at any universe level
#check myId Nat 42         -- α = Nat (in Type 0)
#check myId (Type 0) Nat   -- α = Type 0 (in Type 1)
-- ANCHOR_END: universe_example

-- ANCHOR: notation_example
-- Prefix: operator before operand
prefix:max "√" => fun (n : Nat) => n * n

#eval √5  -- 25

-- Infix: operator between operands
infix:50 " ⊕ " => fun (a b : Nat) => a + b + 1

#eval 3 ⊕ 4  -- 8

-- Postfix: operator after operand
postfix:max "!" => fun (n : Nat) => n * n

#eval 5!  -- 25

-- Mixfix: multiple tokens with operands interspersed
notation "⟪" a ", " b "⟫" => (a, b)
notation "if'" c "then'" t "else'" e => if c then t else e

#eval ⟪1, 2⟫  -- (1, 2)
#eval if' true then' 42 else' 0  -- 42
-- ANCHOR_END: notation_example

-- ANCHOR: set_option_example
-- set_option configures compiler and elaborator behavior
-- Show implicit arguments that are normally hidden
set_option pp.explicit true in
#check @id Nat 5  -- shows: @id Nat 5 : Nat

-- maxRecDepth controls recursion during elaboration (type-checking),
-- not runtime. #reduce fully unfolds expressions at compile time:
-- #reduce (List.range 500).length  -- ERROR without increased limit
set_option maxRecDepth 4000 in
#reduce (List.range 500).length  -- 500
-- ANCHOR_END: set_option_example

end ZeroToQED.Basics
