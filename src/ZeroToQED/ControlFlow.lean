/-!
# Control Flow, Recursion, Structures, and Inductive Types

Control flow patterns, recursion, and user-defined types.
-/

namespace ZeroToQED.ControlFlow

-- ANCHOR: conditionals
-- If-then-else expressions
def absolute (x : Int) : Int :=
  if x < 0 then -x else x

#eval absolute (-5)   -- 5
#eval absolute 3      -- 3

-- Nested conditionals
def classifyNumber (n : Int) : String :=
  if n < 0 then "negative"
  else if n == 0 then "zero"
  else "positive"

#eval classifyNumber (-10)  -- "negative"
#eval classifyNumber 0      -- "zero"
#eval classifyNumber 42     -- "positive"

-- Conditionals are expressions, not statements
def minValue (a b : Nat) : Nat :=
  if a < b then a else b

#eval minValue 3 7  -- 3
-- ANCHOR_END: conditionals

-- ANCHOR: pattern_matching
-- Pattern matching with match
def describeList {α : Type} (xs : List α) : String :=
  match xs with
  | [] => "empty"
  | [_] => "singleton"
  | [_, _] => "pair"
  | _ => "many elements"

#eval describeList ([] : List Nat)     -- "empty"
#eval describeList [1]                  -- "singleton"
#eval describeList [1, 2]               -- "pair"
#eval describeList [1, 2, 3, 4]         -- "many elements"

-- Matching on multiple values
def fizzbuzz (n : Nat) : String :=
  match n % 3, n % 5 with
  | 0, 0 => "FizzBuzz"
  | 0, _ => "Fizz"
  | _, 0 => "Buzz"
  | _, _ => toString n

#eval (List.range 16).map fizzbuzz
-- ["FizzBuzz", "1", "2", "Fizz", "4", "Buzz", ...]

-- Guards in pattern matching
def classifyAge (age : Nat) : String :=
  match age with
  | 0 => "infant"
  | n => if n < 13 then "child"
         else if n < 20 then "teenager"
         else "adult"

#eval classifyAge 5   -- "child"
#eval classifyAge 15  -- "teenager"
#eval classifyAge 30  -- "adult"
-- ANCHOR_END: pattern_matching

-- ANCHOR: simple_recursion
-- Simple recursion on natural numbers
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 5   -- 120
#eval factorial 10  -- 3628800

-- Recursion on lists
def sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

#eval sum [1, 2, 3, 4, 5]  -- 15

-- Computing the length of a list
def length {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => 1 + length xs

#eval length [1, 2, 3]  -- 3
-- ANCHOR_END: simple_recursion

-- ANCHOR: tail_recursion
-- Naive recursion can overflow the stack for large inputs
-- Tail recursion uses an accumulator to avoid this

-- Tail-recursive factorial
def factorialTR (n : Nat) : Nat :=
  let rec go (acc : Nat) : Nat → Nat
    | 0 => acc
    | k + 1 => go (acc * (k + 1)) k
  go 1 n

#eval factorialTR 20  -- 2432902008176640000

-- Tail-recursive sum
def sumTR (xs : List Nat) : Nat :=
  let rec go (acc : Nat) : List Nat → Nat
    | [] => acc
    | x :: rest => go (acc + x) rest
  go 0 xs

#eval sumTR (List.range 1000)  -- Sum of 0..999

-- Tail-recursive reverse
def reverseTR {α : Type} (xs : List α) : List α :=
  let rec go (acc : List α) : List α → List α
    | [] => acc
    | x :: rest => go (x :: acc) rest
  go [] xs

#eval reverseTR [1, 2, 3, 4, 5]  -- [5, 4, 3, 2, 1]
-- ANCHOR_END: tail_recursion

-- ANCHOR: structural_recursion
-- Lean requires recursion to be well-founded
-- Structural recursion on decreasing arguments is automatic

-- Merge sort: structurally recursive
def merge : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: merge xs (y :: ys)
    else y :: merge (x :: xs) ys

-- Insertion sort is simpler and doesn't need termination proofs
def insert' (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert' x ys

def insertionSort : List Nat → List Nat
  | [] => []
  | x :: xs => insert' x (insertionSort xs)

#eval insertionSort [3, 1, 4, 1, 5, 9, 2, 6]  -- [1, 1, 2, 3, 4, 5, 6, 9]
-- ANCHOR_END: structural_recursion

-- ANCHOR: structures_basic
-- Structures group related data with named fields
structure Point where
  x : Float
  y : Float
  deriving Repr

-- Creating structure instances
def origin : Point := { x := 0.0, y := 0.0 }
def point1 : Point := Point.mk 3.0 4.0
def point2 : Point := ⟨1.0, 2.0⟩

-- Accessing fields
#eval point1.x  -- 3.0
#eval point1.y  -- 4.0

-- Functions on structures
def distance (p : Point) : Float :=
  Float.sqrt (p.x * p.x + p.y * p.y)

#eval distance point1  -- 5.0
-- ANCHOR_END: structures_basic

-- ANCHOR: structures_update
-- Updating structures with "with" syntax
def moveRight (p : Point) (dx : Float) : Point :=
  { p with x := p.x + dx }

def moveUp (p : Point) (dy : Float) : Point :=
  { p with y := p.y + dy }

#eval moveRight origin 5.0  -- { x := 5.0, y := 0.0 }

-- Multiple field updates
def translate (p : Point) (dx dy : Float) : Point :=
  { p with x := p.x + dx, y := p.y + dy }

#eval translate origin 3.0 4.0  -- { x := 3.0, y := 4.0 }
-- ANCHOR_END: structures_update

-- ANCHOR: structures_nested
-- Nested structures
structure Rectangle where
  topLeft : Point
  bottomRight : Point
  deriving Repr

def myRect : Rectangle := {
  topLeft := { x := 0.0, y := 10.0 },
  bottomRight := { x := 10.0, y := 0.0 }
}

def width (r : Rectangle) : Float :=
  r.bottomRight.x - r.topLeft.x

def height (r : Rectangle) : Float :=
  r.topLeft.y - r.bottomRight.y

def area (r : Rectangle) : Float :=
  width r * height r

#eval area myRect  -- 100.0
-- ANCHOR_END: structures_nested

-- ANCHOR: structures_defaults
-- Structures with default values
structure Config where
  host : String := "localhost"
  port : Nat := 8080
  debug : Bool := false
  deriving Repr

-- Use defaults
def defaultConfig : Config := {}

-- Override some defaults
def prodConfig : Config := { host := "api.example.com", port := 443 }

#eval defaultConfig  -- { host := "localhost", port := 8080, debug := false }
#eval prodConfig     -- { host := "api.example.com", port := 443, debug := false }
-- ANCHOR_END: structures_defaults

-- ANCHOR: inductive_enum
-- Simple enumerations
inductive Direction where
  | north
  | south
  | east
  | west
  deriving Repr, DecidableEq

def opposite : Direction → Direction
  | .north => .south
  | .south => .north
  | .east => .west
  | .west => .east

#eval opposite Direction.north  -- Direction.south

-- Starfleet vessel classes
inductive StarshipClass where
  | galaxy      -- Galaxy-class (Enterprise-D)
  | sovereign   -- Sovereign-class (Enterprise-E)
  | defiant     -- Defiant-class (compact warship)
  | intrepid    -- Intrepid-class (Voyager)
  | constitution -- Constitution-class (original Enterprise)
  deriving Repr, DecidableEq

def crewComplement : StarshipClass → Nat
  | .galaxy => 1014       -- Families welcome
  | .sovereign => 855     -- More tactical
  | .defiant => 50        -- Tough little ship
  | .intrepid => 141      -- Long-range science
  | .constitution => 430  -- The classic

#eval crewComplement StarshipClass.defiant  -- 50

-- Enums with associated data (MTG spell types)
inductive Spell where
  | creature (power : Nat) (toughness : Nat) (manaCost : Nat)
  | instant (manaCost : Nat)
  | sorcery (manaCost : Nat)
  | enchantment (manaCost : Nat) (isAura : Bool)
  deriving Repr

def manaCost : Spell → Nat
  | .creature _ _ cost => cost
  | .instant cost => cost
  | .sorcery cost => cost
  | .enchantment cost _ => cost

def canBlock : Spell → Bool
  | .creature _ toughness _ => toughness > 0
  | _ => false

#eval manaCost (Spell.creature 3 3 4)        -- 4 (e.g., a 3/3 for 4 mana)
#eval manaCost (Spell.instant 2)              -- 2 (e.g., Counterspell)
#eval canBlock (Spell.creature 2 1 1)         -- true
#eval canBlock (Spell.enchantment 3 true)     -- false
-- ANCHOR_END: inductive_enum

-- ANCHOR: inductive_recursive
-- Recursive inductive types
inductive BinaryTree (α : Type) where
  | leaf : BinaryTree α
  | node : α → BinaryTree α → BinaryTree α → BinaryTree α
  deriving Repr

-- Building trees
def exampleTree : BinaryTree Nat :=
  .node 1
    (.node 2 .leaf .leaf)
    (.node 3
      (.node 4 .leaf .leaf)
      .leaf)

-- Counting nodes
def BinaryTree.size {α : Type} : BinaryTree α → Nat
  | .leaf => 0
  | .node _ left right => 1 + left.size + right.size

#eval exampleTree.size  -- 4

-- Computing depth
def BinaryTree.depth {α : Type} : BinaryTree α → Nat
  | .leaf => 0
  | .node _ left right => 1 + max left.depth right.depth

#eval exampleTree.depth  -- 3

-- In-order traversal
def BinaryTree.inorder {α : Type} : BinaryTree α → List α
  | .leaf => []
  | .node x left right => left.inorder ++ [x] ++ right.inorder

#eval exampleTree.inorder  -- [2, 1, 4, 3]
-- ANCHOR_END: inductive_recursive

-- ANCHOR: inductive_parameterized
-- Expression trees parameterized by the literal type
inductive Expr (α : Type) where
  | lit : α → Expr α
  | add : Expr α → Expr α → Expr α
  | mul : Expr α → Expr α → Expr α
  deriving Repr

-- Evaluate for any type with Add and Mul instances
def Expr.eval {α : Type} [Add α] [Mul α] : Expr α → α
  | .lit n => n
  | .add e1 e2 => e1.eval + e2.eval
  | .mul e1 e2 => e1.eval * e2.eval

-- Integer expression: (2 + 3) * 4
def intExpr : Expr Int := .mul (.add (.lit 2) (.lit 3)) (.lit 4)
#eval intExpr.eval  -- 20

-- Float expression: (1.5 + 2.5) * 3.0
def floatExpr : Expr Float := .mul (.add (.lit 1.5) (.lit 2.5)) (.lit 3.0)
#eval floatExpr.eval  -- 12.0

-- Map a function over all literals
def Expr.map {α β : Type} (f : α → β) : Expr α → Expr β
  | .lit n => .lit (f n)
  | .add e1 e2 => .add (e1.map f) (e2.map f)
  | .mul e1 e2 => .mul (e1.map f) (e2.map f)

-- Convert int expression to float
def floatFromInt : Expr Float := intExpr.map (fun n => Float.ofInt n)
#eval floatFromInt.eval  -- 20.0
-- ANCHOR_END: inductive_parameterized

-- ANCHOR: mutual_recursion
-- Mutually recursive definitions
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n

  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

#eval isEven 10  -- true
#eval isOdd 7    -- true

-- Mutually recursive types
mutual
  inductive Tree (α : Type) where
    | node : α → Forest α → Tree α

  inductive Forest (α : Type) where
    | nil : Forest α
    | cons : Tree α → Forest α → Forest α
end

-- Example forest
def exampleForest : Forest Nat :=
  .cons (.node 1 .nil)
    (.cons (.node 2 (.cons (.node 3 .nil) .nil))
      .nil)
-- ANCHOR_END: mutual_recursion

end ZeroToQED.ControlFlow
