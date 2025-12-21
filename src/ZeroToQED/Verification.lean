namespace Verification

-- ANCHOR: types
inductive Ty where
  | nat  : Ty
  | bool : Ty
  deriving Repr, DecidableEq

@[reducible] def Ty.denote : Ty → Type
  | .nat  => Nat
  | .bool => Bool
-- ANCHOR_END: types

-- ANCHOR: expr
inductive Expr : Ty → Type where
  | nat  : Nat → Expr .nat
  | bool : Bool → Expr .bool
  | add  : Expr .nat → Expr .nat → Expr .nat
  | mul  : Expr .nat → Expr .nat → Expr .nat
  | lt   : Expr .nat → Expr .nat → Expr .bool
  | eq   : Expr .nat → Expr .nat → Expr .bool
  | and  : Expr .bool → Expr .bool → Expr .bool
  | or   : Expr .bool → Expr .bool → Expr .bool
  | not  : Expr .bool → Expr .bool
  | ite  : {t : Ty} → Expr .bool → Expr t → Expr t → Expr t
-- ANCHOR_END: expr

-- ANCHOR: eval
def Expr.eval : {t : Ty} → Expr t → t.denote
  | _, .nat n      => n
  | _, .bool b     => b
  | _, .add e₁ e₂  => e₁.eval + e₂.eval
  | _, .mul e₁ e₂  => e₁.eval * e₂.eval
  | _, .lt e₁ e₂   => e₁.eval < e₂.eval
  | _, .eq e₁ e₂   => e₁.eval == e₂.eval
  | _, .and e₁ e₂  => e₁.eval && e₂.eval
  | _, .or e₁ e₂   => e₁.eval || e₂.eval
  | _, .not e      => !e.eval
  | _, .ite c t e  => if c.eval then t.eval else e.eval
-- ANCHOR_END: eval

-- ANCHOR: examples
def ex1 : Expr .nat := .add (.nat 2) (.nat 3)
def ex2 : Expr .bool := .lt (.nat 2) (.nat 3)
def ex3 : Expr .nat := .ite (.lt (.nat 2) (.nat 3)) (.nat 10) (.nat 20)
def ex4 : Expr .nat := .mul (.add (.nat 2) (.nat 3)) (.nat 4)

#eval ex1.eval  -- 5
#eval ex2.eval  -- true
#eval ex3.eval  -- 10
#eval ex4.eval  -- 20
-- ANCHOR_END: examples

-- ANCHOR: impossible
/-
def bad : Expr .nat := .add (.nat 1) (.bool true)
-- Error: type mismatch
-/
-- ANCHOR_END: impossible

-- ANCHOR: constfold
def Expr.constFold : {t : Ty} → Expr t → Expr t
  | _, .nat n => .nat n
  | _, .bool b => .bool b
  | _, .add e₁ e₂ =>
    match e₁.constFold, e₂.constFold with
    | .nat n, .nat m => .nat (n + m)
    | e₁', e₂' => .add e₁' e₂'
  | _, .mul e₁ e₂ =>
    match e₁.constFold, e₂.constFold with
    | .nat n, .nat m => .nat (n * m)
    | e₁', e₂' => .mul e₁' e₂'
  | _, .lt e₁ e₂ => .lt e₁.constFold e₂.constFold
  | _, .eq e₁ e₂ => .eq e₁.constFold e₂.constFold
  | _, .and e₁ e₂ => .and e₁.constFold e₂.constFold
  | _, .or e₁ e₂ => .or e₁.constFold e₂.constFold
  | _, .not e => .not e.constFold
  | _, .ite c t e =>
    match c.constFold with
    | .bool true => t.constFold
    | .bool false => e.constFold
    | c' => .ite c' t.constFold e.constFold
-- ANCHOR_END: constfold

-- ANCHOR: correctness
theorem constFold_correct : ∀ {t : Ty} (e : Expr t), e.constFold.eval = e.eval := by
  intro t e
  induction e with
  | nat n => rfl
  | bool b => rfl
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.constFold, Expr.eval]
    cases he₁ : e₁.constFold <;> cases he₂ : e₂.constFold <;>
      simp only [Expr.eval, ← ih₁, ← ih₂, he₁, he₂]
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.constFold, Expr.eval]
    cases he₁ : e₁.constFold <;> cases he₂ : e₂.constFold <;>
      simp only [Expr.eval, ← ih₁, ← ih₂, he₁, he₂]
  | lt e₁ e₂ ih₁ ih₂ => simp only [Expr.constFold, Expr.eval, ih₁, ih₂]
  | eq e₁ e₂ ih₁ ih₂ => simp only [Expr.constFold, Expr.eval, ih₁, ih₂]
  | and e₁ e₂ ih₁ ih₂ => simp only [Expr.constFold, Expr.eval, ih₁, ih₂]
  | or e₁ e₂ ih₁ ih₂ => simp only [Expr.constFold, Expr.eval, ih₁, ih₂]
  | not e ih => simp only [Expr.constFold, Expr.eval, ih]
  | ite c t e ihc iht ihe =>
    simp only [Expr.constFold, Expr.eval]
    cases hc : c.constFold <;> simp only [Expr.eval, ← ihc, ← iht, ← ihe, hc]
    case bool b => cases b <;> rfl
-- ANCHOR_END: correctness

end Verification
