import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Data Structures in Lean 4

Types for representing data: primitives, collections, and user-defined types.
-/

namespace ZeroToQED.DataStructures

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

end ZeroToQED.DataStructures
