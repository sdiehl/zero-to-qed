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

-- ANCHOR: context
abbrev Ctx := List Ty

inductive Var : Ctx → Ty → Type where
  | zero : ∀ {ctx t}, Var (t :: ctx) t
  | succ : ∀ {ctx t t'}, Var ctx t → Var (t' :: ctx) t

def Env : Ctx → Type
  | []        => Unit
  | (t :: ts) => t.denote × Env ts

def Env.lookup : {ctx : Ctx} → {t : Ty} → Env ctx → Var ctx t → t.denote
  | _ :: _, _, ⟨v, _⟩,  .zero   => v
  | _ :: _, _, ⟨_, vs⟩, .succ i => lookup vs i
-- ANCHOR_END: context

-- ANCHOR: expr
inductive Expr : Ctx → Ty → Type where
  | nat  : ∀ {ctx}, Nat → Expr ctx .nat
  | bool : ∀ {ctx}, Bool → Expr ctx .bool
  | var  : ∀ {ctx t}, Var ctx t → Expr ctx t
  | add  : ∀ {ctx}, Expr ctx .nat → Expr ctx .nat → Expr ctx .nat
  | mul  : ∀ {ctx}, Expr ctx .nat → Expr ctx .nat → Expr ctx .nat
  | lt   : ∀ {ctx}, Expr ctx .nat → Expr ctx .nat → Expr ctx .bool
  | eq   : ∀ {ctx}, Expr ctx .nat → Expr ctx .nat → Expr ctx .bool
  | and  : ∀ {ctx}, Expr ctx .bool → Expr ctx .bool → Expr ctx .bool
  | or   : ∀ {ctx}, Expr ctx .bool → Expr ctx .bool → Expr ctx .bool
  | not  : ∀ {ctx}, Expr ctx .bool → Expr ctx .bool
  | ite  : ∀ {ctx t}, Expr ctx .bool → Expr ctx t → Expr ctx t → Expr ctx t
  | let_ : ∀ {ctx t₁ t₂}, Expr ctx t₁ → Expr (t₁ :: ctx) t₂ → Expr ctx t₂
-- ANCHOR_END: expr

-- ANCHOR: eval
def Expr.eval : {ctx : Ctx} → {t : Ty} → Env ctx → Expr ctx t → t.denote
  | _, .nat,  _,   .nat n      => n
  | _, .bool, _,   .bool b     => b
  | _, _,     env, .var v      => env.lookup v
  | _, .nat,  env, .add e₁ e₂  => e₁.eval env + e₂.eval env
  | _, .nat,  env, .mul e₁ e₂  => e₁.eval env * e₂.eval env
  | _, .bool, env, .lt e₁ e₂   => e₁.eval env < e₂.eval env
  | _, .bool, env, .eq e₁ e₂   => e₁.eval env == e₂.eval env
  | _, .bool, env, .and e₁ e₂  => e₁.eval env && e₂.eval env
  | _, .bool, env, .or e₁ e₂   => e₁.eval env || e₂.eval env
  | _, .bool, env, .not e      => !e.eval env
  | _, _,     env, .ite c t e  => if c.eval env then t.eval env else e.eval env
  | _, _,     env, .let_ e b   => b.eval ⟨e.eval env, env⟩
-- ANCHOR_END: eval

-- ANCHOR: examples
def ex1 : Expr [] .nat := .add (.nat 2) (.nat 3)
def ex2 : Expr [] .bool := .lt (.nat 2) (.nat 3)
def ex3 : Expr [] .nat := .ite (.lt (.nat 2) (.nat 3)) (.nat 10) (.nat 20)
def ex4 : Expr [] .nat := .let_ (.nat 5) (.add (.var .zero) (.var .zero))
def ex5 : Expr [] .nat :=
  .let_ (.nat 3) (.let_ (.nat 4) (.add (.var (.succ .zero)) (.var .zero)))

#eval ex1.eval ()  -- 5
#eval ex2.eval ()  -- true
#eval ex3.eval ()  -- 10
#eval ex4.eval ()  -- 10
#eval ex5.eval ()  -- 7
-- ANCHOR_END: examples

-- ANCHOR: impossible
/-
def bad : Expr [] .nat := .add (.nat 1) (.bool true)
-- Error: type mismatch
-/
-- ANCHOR_END: impossible

-- ANCHOR: constfold
def Expr.constFold : {ctx : Ctx} → {t : Ty} → Expr ctx t → Expr ctx t
  | _, _, .add (.nat n) (.nat m) => .nat (n + m)
  | _, _, .mul (.nat n) (.nat m) => .nat (n * m)
  | _, _, .ite (.bool true) t _  => t.constFold
  | _, _, .ite (.bool false) _ e => e.constFold
  | _, _, .add e₁ e₂  => .add e₁.constFold e₂.constFold
  | _, _, .mul e₁ e₂  => .mul e₁.constFold e₂.constFold
  | _, _, .ite c t e  => .ite c.constFold t.constFold e.constFold
  | _, _, .let_ e b   => .let_ e.constFold b.constFold
  | _, _, e => e
-- ANCHOR_END: constfold

-- ANCHOR: correctness
theorem constFold_correct (e : Expr ctx t) (env : Env ctx) :
    e.constFold.eval env = e.eval env := by
  induction e generalizing env <;>
    simp only [Expr.constFold, Expr.eval, *]
  case add e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.constFold]
    split
    · simp [Expr.eval]
    · simp [Expr.eval, ih₁, ih₂]
  case mul e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.constFold]
    split
    · simp [Expr.eval]
    · simp [Expr.eval, ih₁, ih₂]
  case ite c t e ihc iht ihe =>
    simp only [Expr.constFold]
    split
    · simp [Expr.eval, iht]
    · simp [Expr.eval, ihe]
    · simp [Expr.eval, ihc, iht, ihe]
  case let_ e b ihe ihb =>
    simp [Expr.eval, ihe, ihb]
-- ANCHOR_END: correctness

end Verification
