/-!
# Type Polymorphism, Classes, and Instances
-/

namespace ZeroToQED.Polymorphism

-- ANCHOR: parametric_polymorphism
def identity {α : Type} (x : α) : α := x

#eval identity 42          -- 42
#eval identity "hello"     -- "hello"
#eval identity [1, 2, 3]   -- [1, 2, 3]

def compose {α β γ : Type} (g : β → γ) (f : α → β) : α → γ :=
  fun x => g (f x)

def addOne (x : Nat) : Nat := x + 1
def double (x : Nat) : Nat := x * 2

#eval compose double addOne 5  -- 12

def flip {α β γ : Type} (f : α → β → γ) : β → α → γ :=
  fun b a => f a b

#eval flip Nat.sub 3 10  -- 7
-- ANCHOR_END: parametric_polymorphism

-- ANCHOR: polymorphic_data
def Pair (α β : Type) := α × β

def makePair {α β : Type} (a : α) (b : β) : Pair α β := (a, b)

#eval makePair 1 "one"  -- (1, "one")

inductive Either (α β : Type) where
  | left : α → Either α β
  | right : β → Either α β
  deriving Repr

def mapEither {α β γ : Type} (f : β → γ) : Either α β → Either α γ
  | .left a => .left a
  | .right b => .right (f b)

#eval mapEither (· + 1) (Either.right 5 : Either String Nat)
-- ANCHOR_END: polymorphic_data

-- ANCHOR: implicit_arguments
def listLength {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: rest => 1 + listLength rest

#eval listLength [1, 2, 3]        -- 3
#eval listLength ["a", "b"]       -- 2
#eval @listLength Nat [1, 2, 3]   -- explicit type argument

def firstOrDefault {α : Type} (xs : List α) (default : α) : α :=
  match xs with
  | [] => default
  | x :: _ => x

#eval firstOrDefault [1, 2, 3] 0      -- 1
#eval firstOrDefault ([] : List Nat) 0 -- 0
-- ANCHOR_END: implicit_arguments

-- ANCHOR: instance_implicit
def printTwice {α : Type} [ToString α] (x : α) : String :=
  s!"{x} and {x}"

#eval printTwice 42       -- "42 and 42"
#eval printTwice true     -- "true and true"
#eval printTwice "hi"     -- "hi and hi"

def maximum {α : Type} [Ord α] (xs : List α) : Option α :=
  xs.foldl (init := none) fun acc x =>
    match acc with
    | none => some x
    | some m => if compare x m == .gt then some x else some m

#eval maximum [3, 1, 4, 1, 5, 9]  -- some 9
#eval maximum ["b", "a", "c"]     -- some "c"
-- ANCHOR_END: instance_implicit

-- ANCHOR: typeclass_definition
class Printable (α : Type) where
  format : α → String

instance : Printable Nat where
  format n := s!"Nat({n})"

instance : Printable Bool where
  format b := if b then "yes" else "no"

instance : Printable String where
  format s := s!"\"{s}\""

def showValue {α : Type} [Printable α] (x : α) : String :=
  Printable.format x

#eval showValue 42      -- "Nat(42)"
#eval showValue true    -- "yes"
#eval showValue "test"  -- "\"test\""
-- ANCHOR_END: typeclass_definition

-- ANCHOR: typeclass_polymorphic
instance {α : Type} [Printable α] : Printable (List α) where
  format xs :=
    let items := xs.map Printable.format
    "[" ++ ", ".intercalate items ++ "]"

instance {α β : Type} [Printable α] [Printable β] : Printable (α × β) where
  format p := s!"({Printable.format p.1}, {Printable.format p.2})"

#eval showValue [1, 2, 3]           -- "[Nat(1), Nat(2), Nat(3)]"
#eval showValue (42, true)          -- "(Nat(42), yes)"
#eval showValue [(1, true), (2, false)]
-- ANCHOR_END: typeclass_polymorphic

-- ANCHOR: numeric_classes
class Addable (α : Type) where
  add : α → α → α
  zero : α

instance : Addable Nat where
  add := Nat.add
  zero := 0

instance : Addable Int where
  add := Int.add
  zero := 0

instance : Addable Float where
  add := Float.add
  zero := 0.0

def sumList {α : Type} [Addable α] (xs : List α) : α :=
  xs.foldl Addable.add Addable.zero

#eval sumList [1, 2, 3, 4, 5]           -- 15
#eval sumList [1.5, 2.5, 3.0]           -- 7.0
#eval sumList ([-1, 2, -3] : List Int)  -- -2
-- ANCHOR_END: numeric_classes

-- ANCHOR: extending_classes
class Eq' (α : Type) where
  eq : α → α → Bool

class Ord' (α : Type) extends Eq' α where
  lt : α → α → Bool

instance : Eq' Nat where
  eq := (· == ·)

instance : Ord' Nat where
  eq := (· == ·)
  lt := (· < ·)

def sortedInsert {α : Type} [Ord' α] (x : α) (xs : List α) : List α :=
  match xs with
  | [] => [x]
  | y :: ys => if Ord'.lt x y then x :: y :: ys else y :: sortedInsert x ys

#eval sortedInsert 3 [1, 2, 4, 5]  -- [1, 2, 3, 4, 5]
-- ANCHOR_END: extending_classes

-- ANCHOR: functor_class
class Functor' (F : Type → Type) where
  map : {α β : Type} → (α → β) → F α → F β

instance : Functor' List where
  map := List.map

instance : Functor' Option where
  map f
    | none => none
    | some x => some (f x)

def doubleAll {F : Type → Type} [Functor' F] (xs : F Nat) : F Nat :=
  Functor'.map (· * 2) xs

#eval doubleAll [1, 2, 3]      -- [2, 4, 6]
#eval doubleAll (some 21)      -- some 42
#eval doubleAll (none : Option Nat)  -- none
-- ANCHOR_END: functor_class

-- ANCHOR: multiple_constraints
def showCompare {α : Type} [ToString α] [Ord α] (x y : α) : String :=
  let result := match compare x y with
    | .lt => "less than"
    | .eq => "equal to"
    | .gt => "greater than"
  s!"{x} is {result} {y}"

#eval showCompare 3 5       -- "3 is less than 5"
#eval showCompare "b" "a"   -- "b is greater than a"

def sortAndShow {α : Type} [ToString α] [Ord α] (xs : List α) : String :=
  let sorted := xs.toArray.qsort (compare · · == .lt) |>.toList
  s!"{sorted}"

#eval sortAndShow [3, 1, 4, 1, 5]  -- "[1, 1, 3, 4, 5]"
-- ANCHOR_END: multiple_constraints

-- ANCHOR: deriving
structure Point' where
  x : Nat
  y : Nat
  deriving Repr, BEq, Hashable

#eval Point'.mk 1 2 == Point'.mk 1 2  -- true
#eval Point'.mk 1 2 == Point'.mk 3 4  -- false

inductive Color where
  | red | green | blue
  deriving Repr, DecidableEq

#eval Color.red == Color.red    -- true
#eval Color.red == Color.blue   -- false

structure Person where
  name : String
  age : Nat
  deriving Repr, BEq

def alice : Person := { name := "Alice", age := 30 }
def bob : Person := { name := "Bob", age := 25 }

#eval alice == bob  -- false
#eval repr alice    -- { name := "Alice", age := 30 }
-- ANCHOR_END: deriving

-- ANCHOR: default_methods
class Semigroup (α : Type) where
  append : α → α → α

class Monoid' (α : Type) extends Semigroup α where
  empty : α

def concat {α : Type} [Monoid' α] (xs : List α) : α :=
  xs.foldl Semigroup.append Monoid'.empty

instance : Monoid' String where
  append := String.append
  empty := ""

instance {α : Type} : Monoid' (List α) where
  append := List.append
  empty := []

#eval concat ["Hello", " ", "World"]  -- "Hello World"
#eval concat [[1, 2], [3], [4, 5]]    -- [1, 2, 3, 4, 5]
-- ANCHOR_END: default_methods

end ZeroToQED.Polymorphism
