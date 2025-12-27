import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Basics of Lean 4

Fundamental concepts of Lean 4.
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

-- ANCHOR: fin
-- Fin n is the type of natural numbers less than n
def smallNum : Fin 5 := 3      -- 3 is less than 5
def anotherSmall : Fin 10 := 7 -- 7 is less than 10

-- Fin values carry a proof that they're in bounds
#eval (smallNum : Fin 5).val   -- 3 (the underlying Nat)

-- Useful for array indexing with guaranteed bounds
def safeIndex {α : Type} (arr : Array α) (i : Fin arr.size) : α :=
  arr[i]

-- Fin arithmetic wraps around
#eval (3 : Fin 5) + 4  -- 2 (wraps: 7 mod 5 = 2)
-- ANCHOR_END: fin

-- ANCHOR: fixed_precision
-- Fixed-precision unsigned integers
def byte : UInt8 := 255
def word : UInt16 := 65535
def dword : UInt32 := 0xDEADBEEF
def qword : UInt64 := 0xCAFEBABE12345678

-- Overflow wraps around
#eval (255 : UInt8) + 1  -- 0

-- Size type for platform-dependent sizing
def platformSize : USize := 42

-- Signed fixed-precision integers
def signedByte : Int8 := -128
def signedWord : Int16 := -32768
-- ANCHOR_END: fixed_precision

-- ANCHOR: bitvectors
-- BitVec n is an n-bit vector
def bits8 : BitVec 8 := 0xFF
def bits16 : BitVec 16 := 0xABCD
def bits32 : BitVec 32 := 0xDEADBEEF

-- Bitwise operations
#eval (0b1100 : BitVec 4) &&& 0b1010  -- 0b1000 (AND)
#eval (0b1100 : BitVec 4) ||| 0b1010  -- 0b1110 (OR)
#eval (0b1100 : BitVec 4) ^^^ 0b1010  -- 0b0110 (XOR)
#eval ~~~(0b1100 : BitVec 4)          -- 0b0011 (NOT)

-- Shifts
#eval (0b0001 : BitVec 4) <<< 2  -- 0b0100 (left shift)
#eval (0b1000 : BitVec 4) >>> 2  -- 0b0010 (right shift)
-- ANCHOR_END: bitvectors

-- ANCHOR: floats
-- IEEE 754 double-precision floating-point
def myFloat : Float := 3.14159
def scientific : Float := 6.022e23
def negativeFloat : Float := -273.15

-- Floating-point arithmetic
#eval 3.14 + 2.86    -- 6.0
#eval 10.0 / 3.0     -- 3.333...
#eval Float.sqrt 2.0 -- 1.414...
#eval Float.sin 0.0  -- 0.0
#eval Float.cos 0.0  -- 1.0

-- Special values
#eval (1.0 / 0.0 : Float)   -- inf
#eval (0.0 / 0.0 : Float)   -- nan
-- ANCHOR_END: floats

-- ANCHOR: chars
-- Characters are Unicode scalar values
def letterA : Char := 'A'
def digit : Char := '7'
def unicode : Char := 'λ'
def bear : Char := '🐻'

-- Character properties
#eval 'A'.isAlpha      -- true
#eval '7'.isDigit      -- true
#eval ' '.isWhitespace -- true
#eval 'a'.isLower      -- true
#eval 'A'.isUpper      -- true

-- Character to/from Nat
#eval 'A'.toNat        -- 65
#eval Char.ofNat 65    -- 'A'

-- Case conversion
#eval 'a'.toUpper      -- 'A'
#eval 'Z'.toLower      -- 'z'
-- ANCHOR_END: chars

-- ANCHOR: strings
-- Strings are sequences of characters
def greeting : String := "Hello, Lean!"
def multiline : String := "Line 1\nLine 2\nLine 3"

-- String operations
#eval "Hello".length           -- 5
#eval "Hello".append " World"  -- "Hello World"
#eval "Hello" ++ " " ++ "World" -- "Hello World"
#eval "Hello".toList           -- ['H', 'e', 'l', 'l', 'o']

-- String interpolation
def shipName := "Mistake Not My Current State Of Alarm"
def shipClass := "GCU"
#eval s!"The {shipClass} {shipName} has entered the system."

-- Substring operations
#eval "Hello World".take 5     -- "Hello"
#eval "Hello World".drop 6     -- "World"
#eval "Hello".isPrefixOf "Hello World"  -- true

-- Splitting and joining
#eval "a,b,c".splitOn ","      -- ["a", "b", "c"]
#eval ",".intercalate ["a", "b", "c"]  -- "a,b,c"
-- ANCHOR_END: strings

-- ANCHOR: unit
-- Unit has exactly one value: ()
def nothing : Unit := ()

-- Often used for side-effecting functions
def printAndReturn : IO Unit := do
  IO.println "Side effect!"
  return ()

-- Unit in function types indicates "no meaningful return value"
def greetIO (name : String) : IO Unit :=
  IO.println s!"Hello, {name}!"
-- ANCHOR_END: unit

-- ANCHOR: empty
-- Empty has no values at all
-- It represents impossibility or unreachable code

-- If you have a value of type Empty, you can prove anything
def absurd' {α : Type} (e : Empty) : α :=
  Empty.elim e

-- Empty is useful for marking impossible cases
inductive Void where  -- Custom empty type (equivalent to Empty)
-- ANCHOR_END: empty

-- ANCHOR: booleans
-- Booleans: true and false
def myBool : Bool := true
def myFalse : Bool := false

-- Boolean operations
#eval true && false   -- false (and)
#eval true || false   -- true (or)
#eval !true           -- false (not)
#eval true ^^ false   -- true (xor)

-- Conditionals
def absInt (x : Int) : Int :=
  if x < 0 then -x else x

#eval absInt (-5)  -- 5

-- Boolean decision
#eval if true then "yes" else "no"   -- "yes"
#eval if false then "yes" else "no"  -- "no"
-- ANCHOR_END: booleans

-- ANCHOR: option
-- Option represents a value that may or may not exist
def someValue : Option Nat := some 42
def noValue : Option Nat := none

-- Pattern matching on Option
def getOrDefault (opt : Option Nat) (default : Nat) : Nat :=
  match opt with
  | some x => x
  | none => default

#eval getOrDefault (some 10) 0  -- 10
#eval getOrDefault none 0       -- 0

-- Option combinators
#eval (some 5).map (· * 2)      -- some 10
#eval (none : Option Nat).map (· * 2)  -- none
#eval (some 5).getD 0           -- 5
#eval (none : Option Nat).getD 0       -- 0
#eval (some 5).isSome           -- true
#eval (some 5).isNone           -- false

-- Chaining Options
#eval (some 5).bind (fun x => some (x + 1))  -- some 6
-- ANCHOR_END: option

-- ANCHOR: tuples
-- Tuples combine values of different types
def pair : Nat × String := (42, "answer")
def triple : Nat × String × Bool := (1, "one", true)

-- Accessing tuple elements
#eval pair.1        -- 42
#eval pair.2        -- "answer"
#eval pair.fst      -- 42
#eval pair.snd      -- "answer"

-- Pattern matching on tuples
def swap {α β : Type} (p : α × β) : β × α :=
  let (a, b) := p
  (b, a)

#eval swap (1, "hello")  -- ("hello", 1)

-- Nested tuples
def nested : (Nat × Nat) × String := ((1, 2), "pair")
#eval nested.1.1    -- 1
#eval nested.1.2    -- 2
-- ANCHOR_END: tuples

-- ANCHOR: sum_types
-- Sum types represent a choice between types
def leftValue : Nat ⊕ String := Sum.inl 42
def rightValue : Nat ⊕ String := Sum.inr "hello"

-- Pattern matching on Sum
def describeSum (s : Nat ⊕ String) : String :=
  match s with
  | Sum.inl n => s!"A number: {n}"
  | Sum.inr str => s!"A string: {str}"

#eval describeSum leftValue   -- "A number: 42"
#eval describeSum rightValue  -- "A string: hello"

-- Except is like Sum but for error handling
def divideExcept (x y : Nat) : Except String Nat :=
  if y == 0 then
    Except.error "Division by zero"
  else
    Except.ok (x / y)

#eval divideExcept 10 2   -- Except.ok 5
#eval divideExcept 10 0   -- Except.error "Division by zero"
-- ANCHOR_END: sum_types

-- ANCHOR: lists
-- Linked lists
def myList : List Nat := [1, 2, 3, 4, 5]
def emptyList : List Nat := []

-- List construction
def consExample := 0 :: [1, 2, 3]  -- [0, 1, 2, 3]
def appendExample := [1, 2] ++ [3, 4]  -- [1, 2, 3, 4]

-- Common operations
#eval [1, 2, 3].length       -- 3
#eval [1, 2, 3].head?        -- some 1
#eval [1, 2, 3].tail?        -- some [2, 3]
#eval [1, 2, 3][1]?          -- some 2
#eval [1, 2, 3].reverse      -- [3, 2, 1]

-- Higher-order functions
#eval [1, 2, 3].map (· * 2)  -- [2, 4, 6]
#eval [1, 2, 3, 4].filter (· > 2)  -- [3, 4]
#eval [1, 2, 3, 4].foldl (· + ·) 0  -- 10

-- Cartesian product via flatMap
#eval [1, 2].flatMap (fun x => [10, 20].map (fun y => x + y))  -- [11, 21, 12, 22]
-- ANCHOR_END: lists

-- ANCHOR: arrays
-- Arrays provide O(1) random access
def myArray : Array Nat := #[1, 2, 3, 4, 5]
def emptyArray : Array Nat := #[]

-- Array operations
#eval #[1, 2, 3].size        -- 3
#eval #[1, 2, 3][0]!         -- 1 (panics if out of bounds)
#eval #[1, 2, 3][1]?         -- some 2
#eval #[1, 2, 3][10]?        -- none

-- Modifying arrays (creates new array)
#eval #[1, 2, 3].push 4      -- #[1, 2, 3, 4]
#eval #[1, 2, 3].pop         -- #[1, 2]
#eval #[1, 2, 3].set! 1 99   -- #[1, 99, 3]

-- Conversion
#eval #[1, 2, 3].toList      -- [1, 2, 3]
#eval [1, 2, 3].toArray      -- #[1, 2, 3]

-- Higher-order functions
#eval #[1, 2, 3].map (· * 2)     -- #[2, 4, 6]
#eval #[1, 2, 3, 4].filter (· % 2 == 0)  -- #[2, 4]
-- ANCHOR_END: arrays

-- ANCHOR: bytearrays
-- ByteArray is an efficient array of bytes
def bytes : ByteArray := ByteArray.mk #[0x48, 0x65, 0x6C, 0x6C, 0x6F]

-- Operations
#eval bytes.size                 -- 5
#eval bytes.get! 0               -- 72 (0x48 = 'H')
#eval bytes.toList               -- [72, 101, 108, 108, 111]

-- Convert to/from String (UTF-8)
#eval "Hello".toUTF8             -- ByteArray from string
-- ANCHOR_END: bytearrays

-- ANCHOR: maps_sets
-- HashMap for key-value storage
open Std in
def myMap : HashMap String Nat :=
  HashMap.emptyWithCapacity
    |>.insert "one" 1
    |>.insert "two" 2
    |>.insert "three" 3

#eval myMap.get? "two"     -- some 2
#eval myMap.get? "four"    -- none
#eval myMap.contains "one" -- true
#eval myMap.size           -- 3

-- HashSet for unique elements
open Std in
def mySet : HashSet Nat :=
  HashSet.emptyWithCapacity
    |>.insert 1
    |>.insert 2
    |>.insert 3
    |>.insert 2  -- duplicate ignored

#eval mySet.contains 2     -- true
#eval mySet.contains 5     -- false
#eval mySet.size           -- 3
-- ANCHOR_END: maps_sets

-- ANCHOR: subtypes
-- Subtypes refine a type with a predicate
def Positive := { n : Nat // n > 0 }

def five : Positive := ⟨5, by decide⟩

-- Accessing subtype values
#eval five.val    -- 5 (the underlying Nat)
-- five.property is a proof that 5 > 0

-- Common subtypes
def NonEmptyList (α : Type) := { xs : List α // xs ≠ [] }

def exampleNEL : NonEmptyList Nat :=
  ⟨[1, 2, 3], by decide⟩

-- Safe head function for non-empty lists
def safeHead {α : Type} [Inhabited α] (nel : NonEmptyList α) : α :=
  match nel.val with
  | x :: _ => x
  | [] => default  -- unreachable due to property, but needed for totality

#eval safeHead exampleNEL  -- 1
-- ANCHOR_END: subtypes

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

-- ANCHOR: structures
structure Point where
  x : Float
  y : Float
  deriving Repr

def origin : Point := ⟨0.0, 0.0⟩
def myPoint : Point := { x := 3.0, y := 4.0 }

def distance (p : Point) : Float :=
  Float.sqrt (p.x * p.x + p.y * p.y)

#eval distance myPoint  -- Output: 5.0
-- ANCHOR_END: structures

-- ANCHOR: inductive_types
inductive SpellSchool where
  | abjuration    -- Protective magic
  | conjuration   -- Summoning things from elsewhere
  | divination    -- Knowing things you shouldn't
  | enchantment   -- Making friends (involuntarily)
  | evocation     -- Fireballs, obviously
  | illusion      -- Lying, but with magic
  | necromancy    -- Asking corpses for favors
  | transmutation -- Turning lead into gold (or frogs)
  deriving Repr, DecidableEq

def schoolDanger : SpellSchool → Nat
  | .abjuration    => 1
  | .divination    => 2
  | .illusion      => 3
  | .transmutation => 4
  | .enchantment   => 5
  | .conjuration   => 6
  | .evocation     => 8  -- Fireballs in enclosed spaces
  | .necromancy    => 9  -- Ethical concerns

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

def MyList.length {α : Type} : MyList α → Nat
  | MyList.nil => 0
  | MyList.cons _ tail => 1 + tail.length
-- ANCHOR_END: inductive_types

-- ANCHOR: type_classes
def showTwice {α : Type} [ToString α] (x : α) : String :=
  s!"{x} {x}"

#eval showTwice 42           -- Output: "42 42"
#eval showTwice "hello"      -- Output: "hello hello"
#eval showTwice true         -- Output: "true true"
-- ANCHOR_END: type_classes

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

def lightningBolt : ManaCost := { red := 1 }
def counterspell : ManaCost := { blue := 2 }
def wrath : ManaCost := { white := 2, colorless := 2 }

def myPool : ManaPool := { blue := 3, white := 2, red := 1 }

#eval myPool.canPay lightningBolt  -- true
#eval myPool.canPay counterspell   -- true
#eval myPool.canPay wrath          -- true
-- ANCHOR_END: mtg_mana

-- ANCHOR: fizzbuzz
def fizzbuzz (n : Nat) : String :=
  match n % 3 == 0, n % 5 == 0 with
  | true,  true  => "FizzBuzz"
  | true,  false => "Fizz"
  | false, true  => "Buzz"
  | false, false => toString n

def runFizzbuzz (limit : Nat) : List String :=
  (List.range limit).map fun i => fizzbuzz (i + 1)

#eval runFizzbuzz 15
-- ANCHOR_END: fizzbuzz

-- ANCHOR: word_frequency
open Std in
def wordFrequency (text : String) : HashMap String Nat :=
  let words := text.toLower.splitOn " "
  words.foldl (init := HashMap.emptyWithCapacity) fun acc word =>
    let count := acc.getD word 0
    acc.insert word (count + 1)

#eval (wordFrequency "the quick brown fox jumps over the lazy dog").toList
-- ANCHOR_END: word_frequency

-- ANCHOR: collatz
/-- The Collatz conjecture: every positive integer eventually reaches 1.
    Unproven since 1937, but we can at least watch the journey. -/
def collatzStep (n : Nat) : Nat :=
  if n % 2 == 0 then n / 2 else 3 * n + 1

def collatzSequence (n : Nat) (fuel : Nat := 1000) : List Nat :=
  match fuel with
  | 0 => [n]  -- give up, though Collatz would be disappointed
  | fuel' + 1 =>
    if n <= 1 then [n]
    else n :: collatzSequence (collatzStep n) fuel'

def collatzLength (n : Nat) : Nat :=
  (collatzSequence n).length

-- The famous 27: takes 111 steps and peaks at 9232
#eval collatzSequence 27
#eval collatzLength 27

-- Find the longest sequence for starting values 1 to n
def longestCollatz (n : Nat) : Nat × Nat :=
  (List.range n).map (· + 1)
    |>.map (fun k => (k, collatzLength k))
    |>.foldl (fun acc pair => if pair.2 > acc.2 then pair else acc) (1, 1)

#eval longestCollatz 100  -- (97, 119)
-- ANCHOR_END: collatz

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
