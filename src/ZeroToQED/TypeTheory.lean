import Mathlib.Tactic.NormNum

/-!
# Type Theory in Lean

This module explores Lean's type system based on dependent type theory,
incorporating concepts from the official Lean 4 language reference.
-/

namespace ZeroToQED.TypeTheory

-- ANCHOR: type_system_overview
example : (fun x => x + 1) 2 = 3 := rfl  -- β-reduction

def myConst := 42
example : myConst = 42 := rfl  -- δ-reduction

example : let x := 5; x + x = 10 := rfl  -- ζ-reduction
-- ANCHOR_END: type_system_overview

-- ANCHOR: functions_dependent
-- Non-dependent function: return type is fixed
-- Similar to Haskell: not :: Bool -> Bool
-- or OCaml: let not : bool -> bool
def double (n : Nat) : Nat := n * 2

-- Another non-dependent example (like Haskell's const)
def constantFive (_ : Nat) : Nat := 5

-- Dependent function: return type depends on the input value
-- This has NO equivalent in Haskell or OCaml!
def makeVec (n : Nat) : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩

-- A more dramatic dependent function example
-- The return TYPE changes based on the input VALUE
def two (b : Bool) : if b then Unit × Unit else String :=
  match b with
  | true => ((), ())    -- Returns a pair of units
  | false => "two"      -- Returns a string

-- This function returns different TYPES based on input:
-- two true : Unit × Unit
-- two false : String

-- Dependent pairs: the second type depends on the first value
def dependentPair : (n : Nat) × Fin n :=
  ⟨5, 3⟩  -- Second component must be less than first

-- Compare with non-dependent versions:
-- Haskell: (Int, Int) -- no constraint between components
-- OCaml: int * int    -- no constraint between components
-- Lean enforces the invariant in the type!

-- Function composition (non-dependent)
def comp {α β γ : Type} (f : β → γ) (g : α → β) : α → γ :=
  fun x => f (g x)

-- This is like Haskell's (.) or OCaml's (@@)
-- But Lean can also do DEPENDENT composition!

-- Dependent function composition
def depComp {α : Type} {β : α → Type} {γ : (x : α) → β x → Type}
    (f : (x : α) → (y : β x) → γ x y)
    (g : (x : α) → β x) :
    (x : α) → γ x (g x) :=
  fun x => f x (g x)

-- Multiple parameters via currying (named after Haskell B. Curry)
def curriedAdd : Nat → Nat → Nat := fun x y => x + y

-- Function extensionality: equal outputs for equal inputs
theorem funext_example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g :=
  funext h
-- ANCHOR_END: functions_dependent

-- ANCHOR: functions_implicit
-- Implicit parameters (inferred from usage)
def implicitId {α : Type} (x : α) : α := x

-- Strict implicit (must be inferrable at application site)
def strictImplicit ⦃α : Type⦄ (x : α) : α := x

-- Auto parameters (filled by type class resolution)
def autoParam {α : Type} [Inhabited α] : α := default

-- Optional parameters with default values
def withDefault (n : Nat := 10) : Nat := n * 2

example : implicitId 5 = 5 := rfl
example : withDefault = 20 := rfl
example : withDefault 3 = 6 := rfl
-- ANCHOR_END: functions_implicit

-- ANCHOR: functions_currying
/-!
### Currying

Currying is the transformation of functions with multiple parameters into
a sequence of functions, each taking a single parameter. In Lean, all
multi-parameter functions are automatically curried.
-/

-- Multi-parameter function (automatically curried)
def add3 (x y z : Nat) : Nat := x + y + z

-- Equivalent to nested lambdas
def add3' : Nat → Nat → Nat → Nat :=
  fun x => fun y => fun z => x + y + z

-- Partial application creates new functions
def add10 : Nat → Nat → Nat := add3 10
def add10And5 : Nat → Nat := add3 10 5

example : add10 3 7 = 20 := rfl
example : add10And5 2 = 17 := rfl

-- Function.curry: Convert uncurried to curried
def uncurriedAdd : Nat × Nat → Nat := fun p => p.1 + p.2
def curriedVer := Function.curry uncurriedAdd

example : curriedVer 3 4 = 7 := rfl

-- Function.uncurry: Convert curried to uncurried
def addPair := Function.uncurry Nat.add
example : addPair (3, 4) = 7 := rfl

-- Currying with dependent types
def depCurry {α : Type} {β : α → Type} {γ : (a : α) → β a → Type}
    (f : (p : (a : α) × β a) → γ p.1 p.2) :
    (a : α) → (b : β a) → γ a b :=
  fun a b => f ⟨a, b⟩
-- ANCHOR_END: functions_currying

-- ANCHOR: functions_extensionality
/-!
### Extensionality

Function extensionality states that two functions are equal if they
produce equal outputs for all inputs. This is not provable from the
other axioms and is added as an axiom in Lean.
-/

-- funext: Basic function extensionality
theorem my_funext {α β : Type} (f g : α → β) :
    (∀ x, f x = g x) → f = g :=
  funext

-- Example: Proving function equality
def double' (n : Nat) : Nat := 2 * n
def double'' (n : Nat) : Nat := n + n

theorem doubles_equal : double' = double'' := by
  funext n
  simp [double', double'']
  omega

-- Dependent function extensionality
theorem dep_funext {α : Type} {β : α → Type}
    (f g : (x : α) → β x) :
    (∀ x, f x = g x) → f = g :=
  funext

-- Eta reduction: λ x, f x = f
theorem eta_reduction (f : Nat → Nat) : (fun x => f x) = f :=
  funext fun _ => rfl

-- Functions equal by behavior, not syntax
def addOne : Nat → Nat := fun x => x + 1
def succFunc : Nat → Nat := Nat.succ

theorem addOne_eq_succ : addOne = succFunc := by
  funext x
  simp [addOne, succFunc]
-- ANCHOR_END: functions_extensionality

-- ANCHOR: functions_totality
/-!
### Totality and Termination

All functions in Lean must be total (defined for all inputs) and
terminating. Lean uses well-founded recursion to ensure termination.
-/

-- Total function: defined for all natural numbers
def safeDivide (n : Nat) (m : Nat) : Nat :=
  if m = 0 then 0 else n / m  -- Returns 0 for division by zero

-- Structural recursion (automatically proven terminating)
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

-- Well-founded recursion with explicit termination proof
def gcd (a b : Nat) : Nat :=
  if h : b = 0 then
    a
  else
    have : a % b < b := Nat.mod_lt _ (Nat.pos_of_ne_zero h)
    gcd b (a % b)
termination_by b

-- Mutual recursion with termination
mutual
  def isEvenMut : Nat → Bool
    | 0 => true
    | n + 1 => isOddMut n

  def isOddMut : Nat → Bool
    | 0 => false
    | n + 1 => isEvenMut n
end

-- Using decreasing_by for custom termination proof
def ackermann : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ackermann m 1
  | m + 1, n + 1 => ackermann m (ackermann (m + 1) n)
termination_by m n => (m, n)
-- ANCHOR_END: functions_totality

-- ANCHOR: functions_api
/-!
### Function API Reference

Lean provides standard function combinators in the Function namespace.
-/

-- Function.comp: Function composition
def composed := Function.comp (· + 10) (· * 2)
example : composed 5 = 20 := rfl  -- (5 * 2) + 10 = 20

-- Using ∘ notation for composition
open Function in
def composed' := (· + 10) ∘ (· * 2)
example : composed' 5 = 20 := rfl

-- Function.const: Constant function
def alwaysFive := Function.const Nat 5
example : alwaysFive 100 = 5 := rfl
example : alwaysFive 999 = 5 := rfl

-- id: Identity function
example : id 42 = 42 := rfl
example : (id ∘ id) = (id : Nat → Nat) := rfl

-- flip: Swap arguments
def subtract (a b : Nat) : Int := a - b
def flippedSubtract := flip subtract
example : subtract 10 3 = 7 := rfl
example : flippedSubtract 3 10 = 7 := rfl

-- Function composition laws
open Function in
theorem comp_assoc {α β γ δ : Type} (f : γ → δ) (g : β → γ) (h : α → β) :
    (f ∘ g) ∘ h = f ∘ (g ∘ h) := rfl

open Function in
theorem id_comp {α β : Type} (f : α → β) :
    id ∘ f = f := rfl

open Function in
theorem comp_id {α β : Type} (f : α → β) :
    f ∘ id = f := rfl
-- ANCHOR_END: functions_api

-- ANCHOR: functions_properties
/-!
### Function Properties

Important mathematical properties of functions.
-/

-- Injective: Different inputs give different outputs
def isInjective {α β : Type} (f : α → β) : Prop :=
  ∀ x y, f x = f y → x = y

theorem double_injective : isInjective (fun n : Nat => 2 * n) := by
  intro x y h
  simp only [] at h
  -- If 2*x = 2*y, then x = y
  have : x * 2 = y * 2 := by rw [mul_comm x 2, mul_comm y 2]; exact h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) this

-- Using Lean's built-in Function.Injective
example : Function.Injective (fun n : Nat => 2 * n) := by
  intro x y h
  simp only [] at h
  have : x * 2 = y * 2 := by rw [mul_comm x 2, mul_comm y 2]; exact h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) this

-- Surjective: Every output is reached by some input
def isSurjective {α β : Type} (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b

-- Not surjective: doubling doesn't produce odd numbers
theorem double_not_surjective :
    ¬Function.Surjective (fun n : Nat => 2 * n) := by
  intro h
  obtain ⟨n, hn⟩ := h 1
  simp at hn
  -- 2*n is always even, but 1 is odd
  cases n with
  | zero => simp at hn
  | succ m => simp [Nat.mul_succ] at hn

-- Bijective: Both injective and surjective
def isBijective {α β : Type} (f : α → β) : Prop :=
  Function.Injective f ∧ Function.Surjective f

-- Left inverse: g ∘ f = id
theorem has_left_inverse {α β : Type} (f : α → β) (g : β → α) :
    Function.LeftInverse g f ↔ ∀ a, g (f a) = a := by
  rfl

-- Right inverse: f ∘ g = id
theorem has_right_inverse {α β : Type} (f : α → β) (g : β → α) :
    Function.RightInverse g f ↔ ∀ b, f (g b) = b := by
  rfl

-- Example: Successor and predecessor
def succInt : Int → Int := (· + 1)
def predInt : Int → Int := (· - 1)

theorem succ_pred_inverse :
    Function.LeftInverse predInt succInt ∧
    Function.RightInverse predInt succInt := by
  constructor <;> intro x <;> simp [succInt, predInt]

-- Inverse functions
structure IsInverse {α β : Type} (f : α → β) (g : β → α) : Prop where
  left : Function.LeftInverse g f
  right : Function.RightInverse g f

theorem inverse_bijective {α β : Type} (f : α → β) (g : β → α)
    (h : IsInverse f g) : isBijective f := by
  constructor
  · -- Injective
    intro x y hxy
    have : g (f x) = g (f y) := by rw [hxy]
    rw [h.left x, h.left y] at this
    exact this
  · -- Surjective
    intro b
    use g b
    exact h.right b
-- ANCHOR_END: functions_properties

-- ANCHOR: propositions_core
-- Basic logical connectives
theorem and_intro (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := ⟨hp, hq⟩

theorem or_elim (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R :=
  h.elim hp hq

theorem iff_intro (P Q : Prop) (hpq : P → Q) (hqp : Q → P) : P ↔ Q :=
  ⟨hpq, hqp⟩

-- Proof irrelevance demonstration
theorem proof_irrel_demo (P : Prop) (p1 p2 : P) : p1 = p2 := rfl

-- Classical logic (via choice)
open Classical in
theorem excluded_middle (P : Prop) : P ∨ ¬P := Classical.em P
-- ANCHOR_END: propositions_core

-- ANCHOR: propositions_decidable
-- Custom decidable instance
instance decidableEven (n : Nat) : Decidable (n % 2 = 0) :=
  if h : n % 2 = 0 then isTrue h else isFalse h

-- Using decidability for computation
def isEven (n : Nat) : Bool := decide (n % 2 = 0)

example : isEven 4 = true := rfl
example : isEven 5 = false := rfl

-- Subsingletons: types with at most one element
theorem subsingleton_prop (P : Prop) : Subsingleton P :=
  ⟨fun _ _ => rfl⟩
-- ANCHOR_END: propositions_decidable

-- ANCHOR: universes_hierarchy
universe u v w

-- Universe polymorphism (explicit universe level)
def polyIdentity (α : Sort u) (a : α) : α := a

-- Universe level expressions
def maxLevel (α : Type u) (β : Type v) : Type (max u v) := α × β

-- Type 0 contains types, Type 1 contains Type 0, etc.
example : Type 0 = Sort 1 := rfl
example : Prop = Sort 0 := rfl

-- Impredicative Prop: functions into Prop stay in Prop
def propPredicate (P : Type u → Prop) : Prop := ∀ α, P α

-- Predicative Type: function types take maximum universe
def typePredicate (P : Type u → Type v) : Type (max (u+1) v) :=
  ∀ α, P α
-- ANCHOR_END: universes_hierarchy

-- ANCHOR: predicativity
-- Predicative: quantifying over Type u produces Type (u+1)
-- The result must be "larger" than what we quantify over
def predicativeExample : Type 1 := ∀ (α : Type 0), α → α

-- Check the universe levels explicitly
#check (∀ (α : Type 0), α → α : Type 1)  -- Lives in Type 1
#check (∀ (α : Type 1), α → α : Type 2)  -- Lives in Type 2

-- Impredicative: quantifying over Prop still produces Prop
-- Prop can "talk about itself" without ascending universe levels
def impredicativeExample : Prop := ∀ (P : Prop), P → P

#check (∀ (P : Prop), P → P : Prop)  -- Still in Prop, not Type 0!

-- Why this matters: classical logic requires impredicativity
-- "For all propositions P, P or not P" is itself a proposition
def excludedMiddleType : Prop := ∀ (P : Prop), P ∨ ¬P

-- If Prop were predicative, this would be Type 1, breaking classical reasoning
-- Impredicativity lets us define propositions that quantify over all propositions

-- The danger: unrestricted impredicativity leads to paradox
-- Girard's paradox shows Type : Type is inconsistent
-- Lean avoids this by making only Prop impredicative
-- ANCHOR_END: predicativity

-- ANCHOR: universes_lifting
-- PLift: lifts any type by exactly one level
def liftedFalse : Type := PLift False

-- ULift: lifts types by any amount
def liftedNat : Type u := ULift.{u} Nat

-- Lifting and unlifting values
def liftExample : ULift.{1} Nat := ⟨42⟩
example : liftExample.down = 42 := rfl

-- Non-cumulativity: types exist at exactly one level
def needsLifting (α : Type 1) : Type 2 := ULift.{2} α
-- ANCHOR_END: universes_lifting

-- ANCHOR: non_cumulativity
-- In Lean, Nat has type Type 0, not Type 1
#check (Nat : Type 0)    -- works
-- #check (Nat : Type 1) -- would fail: Nat is not in Type 1

-- A function expecting Type 1 cannot accept Nat directly
def wantsType1 (α : Type 1) : Type 1 := α

-- This fails: Nat lives in Type 0, not Type 1
-- def broken := wantsType1 Nat

-- Solution: explicitly lift Nat to Type 1
def works := wantsType1 (ULift Nat)

-- In a cumulative system (like Coq), this would work:
-- def coqStyle := wantsType1 Nat  -- Coq allows this

-- Practical example: polymorphic container at higher universe
def Container (α : Type 1) := List α

-- Cannot directly use Nat
-- def natContainer := Container Nat  -- fails

-- Must lift first
def natContainer := Container (ULift Nat)

-- Extracting values requires unlifting
def sumLifted (xs : List (ULift Nat)) : Nat :=
  xs.foldl (fun acc x => acc + x.down) 0
-- ANCHOR_END: non_cumulativity

-- ANCHOR: inductive_basic_extended
-- Basic inductive with multiple constructors
inductive Color : Type where
  | red | green | blue
  deriving Repr, DecidableEq

-- Parameterized inductive type
inductive Result (ε α : Type) : Type where
  | ok : α → Result ε α
  | error : ε → Result ε α

-- Anonymous constructor syntax for single-constructor types
structure Point where
  x : Float
  y : Float

def origin : Point := ⟨0.0, 0.0⟩
-- ANCHOR_END: inductive_basic_extended

-- ANCHOR: inductive_indexed
-- Vector: length-indexed lists
inductive Vector (α : Type) : Nat → Type where
  | nil : Vector α 0
  | cons : ∀ {n}, α → Vector α n → Vector α (n + 1)

def vectorHead {α : Type} {n : Nat} : Vector α (n + 1) → α
  | Vector.cons a _ => a

-- Even/odd indexed list (from manual)
inductive EvenOddList (α : Type) : Bool → Type where
  | nil : EvenOddList α true
  | cons : ∀ {isEven}, α → EvenOddList α isEven → EvenOddList α (!isEven)

def exampleEvenList : EvenOddList Nat true :=
  EvenOddList.cons 1 (EvenOddList.cons 2 EvenOddList.nil)
-- ANCHOR_END: inductive_indexed

-- ANCHOR: inductive_mutual
mutual
  inductive Tree (α : Type) : Type where
    | leaf : α → Tree α
    | node : Forest α → Tree α

  inductive Forest (α : Type) : Type where
    | nil : Forest α
    | cons : Tree α → Forest α → Forest α
end

-- Nested inductive: recursive through other type constructors
inductive NestedTree (α : Type) : Type where
  | leaf : α → NestedTree α
  | node : List (NestedTree α) → NestedTree α

-- Recursors are automatically generated for pattern matching
def treeSize {α : Type} : Tree α → Nat
  | Tree.leaf _ => 1
  | Tree.node forest => forestSize forest
where forestSize : Forest α → Nat
  | Forest.nil => 0
  | Forest.cons t rest => treeSize t + forestSize rest
-- ANCHOR_END: inductive_mutual

-- ANCHOR: inductive_structures
structure Person where
  name : String
  age : Nat
  email : Option String := none
  deriving Repr

-- Inheritance
structure Student extends Person where
  studentId : Nat
  gpa : Float

-- Field access and update syntax
def alice : Person := { name := "Alice", age := 25 }
def olderAlice := { alice with age := 26 }

example : alice.name = "Alice" := rfl
example : olderAlice.age = 26 := rfl
-- ANCHOR_END: inductive_structures

-- ANCHOR: quotient_basic
-- Simple modulo equivalence relation
def ModRel (n : Nat) : Nat → Nat → Prop :=
  fun a b => a % n = b % n

-- Prove it's an equivalence relation
theorem ModRel.refl (n : Nat) : ∀ x, ModRel n x x :=
  fun _ => rfl

theorem ModRel_symm (n : Nat) : ∀ x y, ModRel n x y → ModRel n y x :=
  fun _ _ h => h.symm

theorem ModRel.trans (n : Nat) : ∀ x y z, ModRel n x y → ModRel n y z → ModRel n x z :=
  fun _ _ _ hxy hyz => Eq.trans hxy hyz

-- Create setoid instance
instance ModSetoid (n : Nat) : Setoid Nat where
  r := ModRel n
  iseqv := {
    refl := ModRel.refl n
    symm := @ModRel_symm n
    trans := @ModRel.trans n
  }

-- Define the quotient type (integers modulo n)
def ZMod (n : Nat) : Type := Quotient (ModSetoid n)
-- ANCHOR_END: quotient_basic

-- ANCHOR: quotient_operations
namespace ZMod

-- Constructor respecting equivalence
def mk (n : Nat) (a : Nat) : ZMod n :=
  Quotient.mk (ModSetoid n) a

-- Addition operation via lifting (simplified - proper proof would be longer)
def add {n : Nat} [NeZero n] : ZMod n → ZMod n → ZMod n :=
  Quotient.lift₂
    (fun a b => mk n ((a + b) % n))
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => by
      apply Quotient.sound
      simp only [ModSetoid] at h₁ h₂ ⊢
      unfold ModRel at h₁ h₂ ⊢
      rw [Nat.add_mod, h₁, h₂, ← Nat.add_mod]
      rfl)

-- Quotient.sound: related elements are equal
theorem mk_eq_of_rel {n : Nat} (a b : Nat) (h : ModRel n a b) :
  mk n a = mk n b :=
  Quotient.sound h

-- Quotient induction principle
theorem ind_on {n : Nat} {P : ZMod n → Prop} (q : ZMod n)
  (h : ∀ a, P (mk n a)) : P q :=
  Quotient.ind h q

end ZMod
-- ANCHOR_END: quotient_operations

-- ANCHOR: constructive_classical
-- Constructive proof: we provide an explicit witness
theorem constructive_exists : ∃ n : Nat, n * n = 4 :=
  ⟨2, rfl⟩  -- The witness is 2, and we can compute 2 * 2 = 4

-- Constructive: we can extract and run the witness
def constructive_even : { n : Nat // n % 2 = 0 } :=
  ⟨4, rfl⟩  -- The subtype bundles value with proof

#eval constructive_even.val  -- Outputs: 4

-- The law of excluded middle itself (classical axiom)
theorem lem (P : Prop) : P ∨ ¬P := Classical.em P

-- Double negation elimination (classical, not constructive)
-- In constructive logic, ¬¬P does not imply P
theorem dne (P : Prop) : ¬¬P → P := Classical.byContradiction

-- Classical proof by contradiction: no even number is odd
theorem even_not_odd (n : Nat) : n % 2 = 0 → ¬(n % 2 = 1) := by
  intro heven hodd
  omega
-- ANCHOR_END: constructive_classical

-- ANCHOR: noncomputable_examples
-- Classical choice: given existence, extract a witness
-- This is noncomputable because we cannot run it
noncomputable def classical_witness (P : Nat → Prop) (h : ∃ n, P n) : Nat :=
  Classical.choose h

-- The witness satisfies the property (but we cannot compute what it is)
theorem classical_witness_spec (P : Nat → Prop) (h : ∃ n, P n) :
    P (classical_witness P h) :=
  Classical.choose_spec h

-- Contrast: decidable existence gives computable witnesses
def decidable_witness (p : Nat → Bool) (bound : Nat) : Nat :=
  -- We can search by enumeration because the domain is finite
  (List.range bound).find? (fun n => p n) |>.getD 0

-- The key insight: constructive proofs compute, classical proofs assert
-- ANCHOR_END: noncomputable_examples

-- ANCHOR: advanced_examples
-- Dependent pairs (Sigma types)
def DependentPair := Σ n : Nat, Fin n

def examplePair : DependentPair := ⟨3, 2⟩

-- Type families and dependent pattern matching
def typeFamily : Nat → Type
  | 0 => Unit
  | 1 => Bool
  | _ => Nat

def familyValue : (n : Nat) → typeFamily n
  | 0 => ()
  | 1 => true
  | n@(_ + 2) => n * 2

-- Well-founded recursion via termination_by
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- Custom well-founded recursion
def div2 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => 1 + div2 n

example : factorial 5 = 120 := rfl
example : div2 10 = 5 := rfl
-- ANCHOR_END: advanced_examples

end ZeroToQED.TypeTheory
