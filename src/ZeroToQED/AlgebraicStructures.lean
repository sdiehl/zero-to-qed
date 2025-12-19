/-!
# Algebraic Structures

Building algebraic structures from first principles using type classes.
We define semigroups, monoids, and groups, then prove fundamental theorems.
-/

namespace ZeroToQED.Algebra

-- ANCHOR: semigroup
-- A semigroup has an associative binary operation
class Semigroup (α : Type) where
  op : α → α → α
  op_assoc : ∀ a b c : α, op (op a b) c = op a (op b c)

-- Notation for our operation
infixl:70 " ⋆ " => Semigroup.op
-- ANCHOR_END: semigroup

-- ANCHOR: monoid
-- A monoid adds an identity element to a semigroup
class Monoid (α : Type) extends Semigroup α where
  e : α
  e_op : ∀ a : α, op e a = a
  op_e : ∀ a : α, op a e = a
-- ANCHOR_END: monoid

-- ANCHOR: group_def
-- A group adds inverses to a monoid
class Group (α : Type) extends Monoid α where
  inv : α → α
  inv_op : ∀ a : α, op (inv a) a = e
  op_inv : ∀ a : α, op a (inv a) = e

-- Notation for inverse
postfix:max "⁻¹" => Group.inv
-- ANCHOR_END: group_def

-- ANCHOR: group_theorems
-- Now we prove fundamental group theorems from the axioms

variable {G : Type} [Group G]

-- Left cancellation: if a ⋆ b = a ⋆ c then b = c
theorem op_left_cancel (a b c : G) (h : a ⋆ b = a ⋆ c) : b = c := by
  have : a⁻¹ ⋆ (a ⋆ b) = a⁻¹ ⋆ (a ⋆ c) := by rw [h]
  simp only [← Semigroup.op_assoc, Group.inv_op, Monoid.e_op] at this
  exact this

-- Right cancellation: if b ⋆ a = c ⋆ a then b = c
theorem op_right_cancel (a b c : G) (h : b ⋆ a = c ⋆ a) : b = c := by
  have : (b ⋆ a) ⋆ a⁻¹ = (c ⋆ a) ⋆ a⁻¹ := by rw [h]
  simp only [Semigroup.op_assoc, Group.op_inv, Monoid.op_e] at this
  exact this

-- The identity is unique
theorem e_unique (e' : G) (h : ∀ a : G, e' ⋆ a = a) : e' = Monoid.e := by
  have : e' ⋆ Monoid.e = Monoid.e := h Monoid.e
  rw [Monoid.op_e] at this
  exact this

-- Inverses are unique
theorem inv_unique (a b : G) (h : b ⋆ a = Monoid.e) : b = a⁻¹ := by
  have step1 : b ⋆ a ⋆ a⁻¹ = Monoid.e ⋆ a⁻¹ := by rw [h]
  simp only [Semigroup.op_assoc, Group.op_inv, Monoid.op_e, Monoid.e_op] at step1
  exact step1

-- Double inverse: (a⁻¹)⁻¹ = a
theorem inv_inv (a : G) : (a⁻¹)⁻¹ = a := by
  symm
  apply inv_unique
  exact Group.op_inv a

-- Inverse of product: (a ⋆ b)⁻¹ = b⁻¹ ⋆ a⁻¹
theorem op_inv_rev (a b : G) : (a ⋆ b)⁻¹ = b⁻¹ ⋆ a⁻¹ := by
  symm
  apply inv_unique
  calc b⁻¹ ⋆ a⁻¹ ⋆ (a ⋆ b)
      = b⁻¹ ⋆ (a⁻¹ ⋆ (a ⋆ b)) := by rw [Semigroup.op_assoc]
    _ = b⁻¹ ⋆ (a⁻¹ ⋆ a ⋆ b) := by rw [← Semigroup.op_assoc a⁻¹ a b]
    _ = b⁻¹ ⋆ (Monoid.e ⋆ b) := by rw [Group.inv_op]
    _ = b⁻¹ ⋆ b := by rw [Monoid.e_op]
    _ = Monoid.e := Group.inv_op b
-- ANCHOR_END: group_theorems

-- ANCHOR: int2_def
-- Example: Integers mod 2 form a group under addition

inductive Z2 : Type where
  | zero : Z2
  | one : Z2
  deriving DecidableEq, Repr

def Z2.add : Z2 → Z2 → Z2
  | .zero, a => a
  | .one, .zero => .one
  | .one, .one => .zero

def Z2.neg : Z2 → Z2
  | a => a  -- In Z2, every element is its own inverse
-- ANCHOR_END: int2_def

-- ANCHOR: int2_group
instance : Group Z2 where
  op := Z2.add
  op_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  e := Z2.zero
  e_op := by
    intro a
    cases a <;> rfl
  op_e := by
    intro a
    cases a <;> rfl
  inv := Z2.neg
  inv_op := by
    intro a
    cases a <;> rfl
  op_inv := by
    intro a
    cases a <;> rfl

-- Test computation
#eval (Z2.one ⋆ Z2.one : Z2)  -- zero
#eval (Z2.one ⋆ Z2.zero : Z2) -- one
-- ANCHOR_END: int2_group

-- ANCHOR: int2_theorems
-- Verify our theorems work on the concrete example
example : (Z2.one)⁻¹ = Z2.one := rfl
example : Z2.one ⋆ Z2.one⁻¹ = Z2.zero := rfl

theorem z2_self_inverse (a : Z2) : a ⋆ a = Monoid.e := by
  cases a <;> rfl

-- Z2 is commutative
theorem z2_comm (a b : Z2) : a ⋆ b = b ⋆ a := by
  cases a <;> cases b <;> rfl
-- ANCHOR_END: int2_theorems

-- ANCHOR: comm_group
-- Commutative (Abelian) groups
class CommGroup (α : Type) extends Group α where
  op_comm : ∀ a b : α, Semigroup.op a b = Semigroup.op b a

instance : CommGroup Z2 where
  op_comm := z2_comm
-- ANCHOR_END: comm_group

-- ANCHOR: vector_space_def
-- A simple 2D vector space over integers

structure Vec2 where
  x : Int
  y : Int
  deriving DecidableEq, Repr

def Vec2.add (v w : Vec2) : Vec2 :=
  ⟨v.x + w.x, v.y + w.y⟩

def Vec2.neg (v : Vec2) : Vec2 :=
  ⟨-v.x, -v.y⟩

def Vec2.zero : Vec2 := ⟨0, 0⟩

def Vec2.smul (c : Int) (v : Vec2) : Vec2 :=
  ⟨c * v.x, c * v.y⟩

infixl:65 " +ᵥ " => Vec2.add
prefix:100 "-ᵥ" => Vec2.neg
infixl:70 " •ᵥ " => Vec2.smul
-- ANCHOR_END: vector_space_def

-- ANCHOR: vector_space_group
-- Vec2 forms a group under addition
theorem vec2_inv_op (a : Vec2) : Vec2.add (Vec2.neg a) a = Vec2.zero := by
  simp only [Vec2.add, Vec2.neg, Vec2.zero, Int.add_comm, Int.add_right_neg]

theorem vec2_op_inv (a : Vec2) : Vec2.add a (Vec2.neg a) = Vec2.zero := by
  simp only [Vec2.add, Vec2.neg, Vec2.zero, Int.add_right_neg]

instance : Group Vec2 where
  op := Vec2.add
  op_assoc := by
    intro a b c
    simp only [Vec2.add, Int.add_assoc]
  e := Vec2.zero
  e_op := by
    intro a
    simp only [Vec2.add, Vec2.zero, Int.zero_add]
  op_e := by
    intro a
    simp only [Vec2.add, Vec2.zero, Int.add_zero]
  inv := Vec2.neg
  inv_op := vec2_inv_op
  op_inv := vec2_op_inv

-- Vec2 is commutative
theorem vec2_comm (a b : Vec2) : a ⋆ b = b ⋆ a := by
  show Vec2.add a b = Vec2.add b a
  simp only [Vec2.add, Int.add_comm]

instance : CommGroup Vec2 where
  op_comm := vec2_comm
-- ANCHOR_END: vector_space_group

-- ANCHOR: vector_space_theorems
-- Scalar multiplication properties
theorem smul_zero (c : Int) : c •ᵥ Vec2.zero = Vec2.zero := by
  simp only [Vec2.smul, Vec2.zero, Int.mul_zero]

theorem zero_smul (v : Vec2) : (0 : Int) •ᵥ v = Vec2.zero := by
  simp only [Vec2.smul, Vec2.zero, Int.zero_mul]

theorem one_smul (v : Vec2) : (1 : Int) •ᵥ v = v := by
  simp only [Vec2.smul, Int.one_mul]

theorem smul_add (c : Int) (v w : Vec2) :
    c •ᵥ (v +ᵥ w) = (c •ᵥ v) +ᵥ (c •ᵥ w) := by
  simp only [Vec2.smul, Vec2.add, Int.mul_add]

theorem add_smul (c d : Int) (v : Vec2) :
    (c + d) •ᵥ v = (c •ᵥ v) +ᵥ (d •ᵥ v) := by
  simp only [Vec2.smul, Vec2.add, Int.add_mul]

theorem smul_smul (c d : Int) (v : Vec2) :
    c •ᵥ (d •ᵥ v) = (c * d) •ᵥ v := by
  simp only [Vec2.smul, Int.mul_assoc]
-- ANCHOR_END: vector_space_theorems

-- ANCHOR: vector_examples
-- Concrete computations
def v1 : Vec2 := ⟨1, 2⟩
def v2 : Vec2 := ⟨3, 4⟩

#eval v1 +ᵥ v2           -- { x := 4, y := 6 }
#eval 2 •ᵥ v1            -- { x := 2, y := 4 }
#eval v1 +ᵥ (-ᵥv1)       -- { x := 0, y := 0 }

-- The group inverse works correctly
example : v1 +ᵥ (-ᵥv1) = Vec2.zero := by rfl
-- ANCHOR_END: vector_examples

-- ANCHOR: ring_def
-- A ring combines two structures: an abelian group under addition
-- and a monoid under multiplication, linked by distributivity

class Ring (α : Type) where
  -- Additive abelian group
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  add_zero : ∀ a, add a zero = a
  neg_add : ∀ a, add (neg a) a = zero
  add_comm : ∀ a b, add a b = add b a
  -- Multiplicative monoid
  mul : α → α → α
  one : α
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  -- Distributivity connects the two structures
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
-- ANCHOR_END: ring_def

-- ANCHOR: ring_theorems
variable {R : Type} [Ring R]

-- Zero times anything is zero (a theorem, not an axiom)
theorem ring_zero_mul (a : R) : Ring.mul Ring.zero a = Ring.zero := by
  have h : Ring.add (Ring.mul Ring.zero a) (Ring.mul Ring.zero a) =
           Ring.add (Ring.mul Ring.zero a) Ring.zero := by
    calc Ring.add (Ring.mul Ring.zero a) (Ring.mul Ring.zero a)
        = Ring.mul (Ring.add Ring.zero Ring.zero) a := by rw [Ring.right_distrib]
      _ = Ring.mul Ring.zero a := by rw [Ring.zero_add]
      _ = Ring.add (Ring.mul Ring.zero a) Ring.zero := by rw [Ring.add_zero]
  have cancel : ∀ x y z : R, Ring.add x y = Ring.add x z → y = z := by
    intro x y z heq
    have h1 : Ring.add (Ring.neg x) (Ring.add x y) =
              Ring.add (Ring.neg x) (Ring.add x z) := by rw [heq]
    simp only [← Ring.add_assoc, Ring.neg_add, Ring.zero_add] at h1
    exact h1
  exact cancel _ _ _ h

theorem ring_mul_zero (a : R) : Ring.mul a Ring.zero = Ring.zero := by
  have h : Ring.add (Ring.mul a Ring.zero) (Ring.mul a Ring.zero) =
           Ring.add (Ring.mul a Ring.zero) Ring.zero := by
    calc Ring.add (Ring.mul a Ring.zero) (Ring.mul a Ring.zero)
        = Ring.mul a (Ring.add Ring.zero Ring.zero) := by rw [Ring.left_distrib]
      _ = Ring.mul a Ring.zero := by rw [Ring.zero_add]
      _ = Ring.add (Ring.mul a Ring.zero) Ring.zero := by rw [Ring.add_zero]
  have cancel : ∀ x y z : R, Ring.add x y = Ring.add x z → y = z := by
    intro x y z heq
    have h1 : Ring.add (Ring.neg x) (Ring.add x y) =
              Ring.add (Ring.neg x) (Ring.add x z) := by rw [heq]
    simp only [← Ring.add_assoc, Ring.neg_add, Ring.zero_add] at h1
    exact h1
  exact cancel _ _ _ h
-- ANCHOR_END: ring_theorems

-- ANCHOR: integers_ring
-- The integers form a ring
instance intRing : Ring Int where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  mul := (· * ·)
  one := 1
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  neg_add := Int.add_left_neg
  add_comm := Int.add_comm
  mul_assoc := Int.mul_assoc
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
-- ANCHOR_END: integers_ring

-- ANCHOR: involutive_abelian
-- If every element is its own inverse, the group must be abelian.
-- The proof: ab = (ab)⁻¹ = b⁻¹a⁻¹ = ba. Constraints beget structure.
theorem involutive_imp_comm {G : Type} [Group G]
    (h : ∀ g : G, g ⋆ g = Monoid.e) : ∀ a b : G, a ⋆ b = b ⋆ a := by
  intro a b
  -- Key insight: if g² = e then g = g⁻¹
  have inv_self : ∀ g : G, g = g⁻¹ := fun g => by
    have := h g
    calc g = g ⋆ Monoid.e := (Monoid.op_e _).symm
      _ = g ⋆ (g ⋆ g⁻¹) := by rw [Group.op_inv]
      _ = (g ⋆ g) ⋆ g⁻¹ := (Semigroup.op_assoc _ _ _).symm
      _ = Monoid.e ⋆ g⁻¹ := by rw [this]
      _ = g⁻¹ := Monoid.e_op _
  -- Now: ab = (ab)⁻¹ = b⁻¹a⁻¹ = ba
  calc a ⋆ b
      = (a ⋆ b)⁻¹ := inv_self (a ⋆ b)
    _ = b⁻¹ ⋆ a⁻¹ := op_inv_rev a b
    _ = b ⋆ a := by rw [← inv_self a, ← inv_self b]
-- ANCHOR_END: involutive_abelian

-- ANCHOR: exercise_square_commutes
-- Exercise: If squaring distributes, the group is abelian.
-- Hint: expand (ab)² = a²b² and cancel to get ab = ba.
theorem square_distrib_imp_comm {G : Type} [Group G]
    (h : ∀ a b : G, (a ⋆ b) ⋆ (a ⋆ b) = (a ⋆ a) ⋆ (b ⋆ b)) :
    ∀ a b : G, a ⋆ b = b ⋆ a := by
  sorry
-- ANCHOR_END: exercise_square_commutes

end ZeroToQED.Algebra
