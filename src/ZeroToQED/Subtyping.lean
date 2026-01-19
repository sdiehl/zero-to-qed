/-!
# Congruence and Subtyping
-/

namespace ZeroToQED.Subtyping

-- ANCHOR: subtype_definition
def Positive := { n : Nat // n > 0 }

def five : Positive := ⟨5, by decide⟩

#eval five.val  -- 5

def NonEmpty (α : Type) := { xs : List α // xs ≠ [] }

def singletonList : NonEmpty Nat := ⟨[42], by decide⟩
-- ANCHOR_END: subtype_definition

-- ANCHOR: subtype_operations
def doublePositive (p : Positive) : Positive :=
  ⟨p.val * 2, Nat.mul_pos p.property (by decide)⟩

#eval (doublePositive five).val  -- 10

def addPositive (a b : Positive) : Positive :=
  ⟨a.val + b.val, Nat.add_pos_left a.property b.val⟩

def safeHead {α : Type} (xs : NonEmpty α) : α :=
  match h : xs.val with
  | x :: _ => x
  | [] => absurd h xs.property
-- ANCHOR_END: subtype_operations

-- ANCHOR: refinement_types
def Even := { n : Nat // n % 2 = 0 }
def Odd := { n : Nat // n % 2 = 1 }

def zero' : Even := ⟨0, rfl⟩
def two' : Even := ⟨2, rfl⟩
def one' : Odd := ⟨1, rfl⟩
def three' : Odd := ⟨3, rfl⟩

def BoundedNat (lo hi : Nat) := { n : Nat // lo ≤ n ∧ n < hi }

def inRange : BoundedNat 0 10 := ⟨5, by omega⟩
-- ANCHOR_END: refinement_types

-- ANCHOR: coercion_basic
instance : Coe Positive Nat where
  coe p := p.val

def useAsNat (p : Positive) : Nat :=
  p + 10

#eval useAsNat five  -- 15

instance {α : Type} : Coe (NonEmpty α) (List α) where
  coe xs := xs.val

def listLength (xs : NonEmpty Nat) : Nat :=
  xs.val.length

#eval listLength singletonList  -- 1
-- ANCHOR_END: coercion_basic

-- ANCHOR: coercion_chain
structure Meters where
  val : Float
  deriving Repr

structure Kilometers where
  val : Float
  deriving Repr

instance : Coe Meters Float where
  coe m := m.val

instance : Coe Kilometers Meters where
  coe km := ⟨km.val * 1000⟩

def addDistances (a : Meters) (b : Kilometers) : Meters :=
  ⟨a.val + (b : Meters).val⟩

#eval addDistances ⟨500⟩ ⟨1.5⟩  -- Meters.mk 2000.0
-- ANCHOR_END: coercion_chain

-- ANCHOR: coercion_function
instance : CoeFun Positive (fun _ => Nat → Nat) where
  coe p := fun n => p.val + n

#eval five 10  -- 15

structure Adder where
  amount : Nat

instance : CoeFun Adder (fun _ => Nat → Nat) where
  coe a := fun n => n + a.amount

def addFive : Adder := ⟨5⟩

#eval addFive 10  -- 15
-- ANCHOR_END: coercion_function

-- ANCHOR: coe_sort
structure Predicate' (α : Type) where
  test : α → Bool

instance {α : Type} : CoeFun (Predicate' α) (fun _ => α → Bool) where
  coe p := p.test

def isEven' : Predicate' Nat := ⟨fun n => n % 2 == 0⟩

#eval isEven' 4   -- true
#eval isEven' 5   -- false
-- ANCHOR_END: coe_sort

-- ANCHOR: congruence_basic
example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  congr

example (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by
  congr

example (a b c d : Nat) (h1 : a = b) (h2 : c = d) : a + c = b + d := by
  congr <;> assumption
-- ANCHOR_END: congruence_basic

-- ANCHOR: congruence_args
example (f : Nat → Nat → Nat) (a b c d : Nat)
    (h1 : a = c) (h2 : b = d) : f a b = f c d := by
  rw [h1, h2]

example (xs ys : List Nat) (h : xs = ys) : xs.length = ys.length := by
  rw [h]
-- ANCHOR_END: congruence_args

-- ANCHOR: subst_rewrite
example (a b : Nat) (h : a = b) : a * a = b * b := by
  subst h
  rfl

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]

example (a b : Nat) (h : a = b) (f : Nat → Nat) : f a = f b := by
  rw [h]
-- ANCHOR_END: subst_rewrite

-- ANCHOR: cast_convert
example (n : Nat) : Int := n

def natToInt (n : Nat) : Int := n

#eval natToInt 42  -- 42

def stringToNat? (s : String) : Option Nat :=
  s.toNat?

#eval stringToNat? "123"   -- some 123
#eval stringToNat? "abc"   -- none
-- ANCHOR_END: cast_convert

-- ANCHOR: decidable_prop
def isPositive (n : Int) : Decidable (n > 0) :=
  if h : n > 0 then isTrue h else isFalse h

def checkPositive (n : Int) : String :=
  if n > 0 then "positive" else "not positive"

#eval checkPositive 5    -- "positive"
#eval checkPositive (-3) -- "not positive"

def decideEqual (a b : Nat) : Decidable (a = b) :=
  if h : a = b then isTrue h else isFalse h
-- ANCHOR_END: decidable_prop

-- ANCHOR: type_class_subtyping
class Animal (α : Type) where
  speak : α → String

class Dog (α : Type) extends Animal α where
  fetch : α → String

structure Labrador where
  name : String

instance : Animal Labrador where
  speak lab := s!"{lab.name} says woof!"

instance : Dog Labrador where
  speak lab := s!"{lab.name} says woof!"
  fetch lab := s!"{lab.name} fetches the ball!"

def makeSpeak {α : Type} [Animal α] (a : α) : String :=
  Animal.speak a

def rex : Labrador := ⟨"Rex"⟩

#eval makeSpeak rex  -- "Rex says woof!"
#eval Dog.fetch rex  -- "Rex fetches the ball!"
-- ANCHOR_END: type_class_subtyping

-- ANCHOR: structure_extension
structure Shape where
  name : String

structure Circle extends Shape where
  radius : Float

structure Rectangle extends Shape where
  width : Float
  height : Float

def myCircle : Circle := { name := "unit circle", radius := 1.0 }
def myRect : Rectangle := { name := "square", width := 2.0, height := 2.0 }

#eval myCircle.name    -- "unit circle"
#eval myCircle.radius  -- 1.0
-- ANCHOR_END: structure_extension

-- ANCHOR: nominal_structural
structure Meters' where
  val : Float

structure Seconds where
  val : Float

def distance : Meters' := ⟨100.0⟩
def time : Seconds := ⟨10.0⟩

abbrev Speed := Float

def calcSpeed (d : Meters') (t : Seconds) : Speed :=
  d.val / t.val

#eval calcSpeed distance time  -- 10.0
-- ANCHOR_END: nominal_structural

end ZeroToQED.Subtyping
