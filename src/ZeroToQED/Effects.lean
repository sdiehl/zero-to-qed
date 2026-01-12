/-!
# Monads: Impurity and Fallibility
-/

namespace ZeroToQED.Monads

-- ANCHOR: option_monad
def safeDivide (x y : Nat) : Option Nat :=
  if y == 0 then none else some (x / y)

def safeHead {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | x :: _ => some x

#eval safeDivide 10 2   -- some 5
#eval safeDivide 10 0   -- none
#eval safeHead [1, 2]   -- some 1
#eval safeHead ([] : List Nat)  -- none
-- ANCHOR_END: option_monad

-- ANCHOR: option_chaining_ugly
def computation (xs : List Nat) : Option Nat :=
  match safeHead xs with
  | none => none
  | some x =>
    match safeDivide 100 x with
    | none => none
    | some y => some (y + 1)

#eval computation [5, 2, 3]   -- some 21
#eval computation [0, 2, 3]   -- none (division by zero)
#eval computation []          -- none (empty list)
-- ANCHOR_END: option_chaining_ugly

-- ANCHOR: option_bind
def computation' (xs : List Nat) : Option Nat :=
  safeHead xs >>= fun x =>
  safeDivide 100 x >>= fun y =>
  some (y + 1)

#eval computation' [5, 2, 3]  -- some 21
#eval computation' [0, 2, 3]  -- none
#eval computation' []         -- none
-- ANCHOR_END: option_bind

-- ANCHOR: do_notation
def computationDo (xs : List Nat) : Option Nat := do
  let x ← safeHead xs
  let y ← safeDivide 100 x
  return y + 1

#eval computationDo [5, 2, 3]  -- some 21
#eval computationDo [0, 2, 3]  -- none
#eval computationDo []         -- none

def validateInput (name : String) (age : Nat) : Option (String × Nat) := do
  if name.isEmpty then none
  if age == 0 then none
  return (name, age)

#eval validateInput "Alice" 30  -- some ("Alice", 30)
#eval validateInput "" 30       -- none
#eval validateInput "Bob" 0     -- none
-- ANCHOR_END: do_notation

-- ANCHOR: except_monad
inductive ValidationError where
  | emptyName
  | invalidAge (age : Nat)
  | missingField (field : String)
  deriving Repr

def validateName (name : String) : Except ValidationError String :=
  if name.isEmpty then .error .emptyName
  else .ok name

def validateAge (age : Nat) : Except ValidationError Nat :=
  if age == 0 || age > 150 then .error (.invalidAge age)
  else .ok age

def validatePerson (name : String) (age : Nat) : Except ValidationError (String × Nat) := do
  let validName ← validateName name
  let validAge ← validateAge age
  return (validName, validAge)

#eval validatePerson "Alice" 30   -- Except.ok ("Alice", 30)
#eval validatePerson "" 30        -- Except.error ValidationError.emptyName
#eval validatePerson "Bob" 200    -- Except.error (ValidationError.invalidAge 200)
-- ANCHOR_END: except_monad

-- ANCHOR: state_monad
abbrev State' (σ α : Type) := σ → (α × σ)

def get'' {σ : Type} : State' σ σ := fun s => (s, s)

def set'' {σ : Type} (newState : σ) : State' σ Unit := fun _ => ((), newState)

def modify'' {σ : Type} (f : σ → σ) : State' σ Unit := fun s => ((), f s)

def runState' {σ α : Type} (init : σ) (m : State' σ α) : α × σ :=
  m init

def counter' : State' Nat Nat := fun n => (n, n + 1)

#eval runState' 0 counter'       -- (0, 1)
#eval runState' 10 counter'      -- (10, 11)
-- ANCHOR_END: state_monad

-- ANCHOR: state_example
def tick : StateM Nat Unit := modify (· + 1)

def getTicks : StateM Nat Nat := get

def countOperations : StateM Nat Nat := do
  tick
  tick
  tick
  let count ← getTicks
  return count

#eval countOperations.run 0    -- (3, 3)
#eval countOperations.run 10   -- (13, 13)
-- ANCHOR_END: state_example

-- ANCHOR: transformer_ordering_minimal
-- Two ways to combine State and Except - the order matters!

-- State outside Except: on error, state is LOST
abbrev Rollback := StateT Nat (Except Unit)

-- Except outside State: on error, state is PRESERVED
abbrev Audit := ExceptT Unit (StateM Nat)

def countThenFailRollback : Rollback Unit := do
  modify (· + 1)  -- count = 1
  modify (· + 1)  -- count = 2
  throw ()        -- error!
  modify (· + 1)  -- never reached

def countThenFailAudit : Audit Unit := do
  modify (· + 1)  -- count = 1
  modify (· + 1)  -- count = 2
  throw ()        -- error!
  modify (· + 1)  -- never reached

-- Rollback: error discards the state
#eval StateT.run countThenFailRollback 0
-- Except.error ()  ← count is gone!

-- Audit: error preserves the state
#eval StateT.run (ExceptT.run countThenFailAudit) 0
-- (Except.error (), 2)  ← count = 2 preserved
-- ANCHOR_END: transformer_ordering_minimal

-- ANCHOR: list_monad
def pairs (xs : List Nat) (ys : List Nat) : List (Nat × Nat) :=
  xs.flatMap fun x => ys.map fun y => (x, y)

#eval pairs [1, 2] [10, 20]  -- [(1, 10), (1, 20), (2, 10), (2, 20)]

def pythagTriples (n : Nat) : List (Nat × Nat × Nat) :=
  (List.range n).flatMap fun a =>
  (List.range n).flatMap fun b =>
  (List.range n).filterMap fun c =>
    if a * a + b * b == c * c && a > 0 && b > 0 then
      some (a, b, c)
    else
      none

#eval pythagTriples 15  -- [(3, 4, 5), (4, 3, 5), (5, 12, 13), ...]
-- ANCHOR_END: list_monad

-- ANCHOR: monad_class
class Monad' (M : Type → Type) extends Functor M where
  pure' : {α : Type} → α → M α
  bind' : {α β : Type} → M α → (α → M β) → M β

instance : Monad' Option where
  map f
    | none => none
    | some x => some (f x)
  pure' := some
  bind' m f := match m with
    | none => none
    | some x => f x

instance : Monad' List where
  map := List.map
  pure' x := [x]
  bind' m f := m.flatMap f
-- ANCHOR_END: monad_class

-- ANCHOR: monad_laws
-- Left identity: pure a >>= f  =  f a
example (f : Nat → Option Nat) (a : Nat) :
    (pure a >>= f) = f a := rfl

-- Right identity: m >>= pure  =  m
example (m : Option Nat) : (m >>= pure) = m := by
  cases m <;> rfl

-- Associativity: (m >>= f) >>= g  =  m >>= (fun x => f x >>= g)
example (m : Option Nat) (f : Nat → Option Nat) (g : Nat → Option Nat) :
    ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by
  cases m <;> rfl
-- ANCHOR_END: monad_laws

-- ANCHOR: early_return
def findFirst {α : Type}
    (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if p x then return x
  none

#eval findFirst (· > 5) [1, 2, 3, 7, 4]  -- some 7
#eval findFirst (· > 10) [1, 2, 3]       -- none

def processUntilError (xs : List Nat) : Except String (List Nat) := do
  let mut results := []
  for x in xs do
    if x == 0 then
      throw "encountered zero"
    results := results ++ [x * 2]
  return results

#eval processUntilError [1, 2, 3]     -- Except.ok [2, 4, 6]
#eval processUntilError [1, 0, 3]     -- Except.error "encountered zero"
-- ANCHOR_END: early_return

-- ANCHOR: combining_monads
def mayFail (x : Nat) : Option Nat :=
  if x == 0 then none else some (100 / x)

def processAll (xs : List Nat) : Option (List Nat) :=
  xs.mapM mayFail

#eval processAll [1, 2, 4, 5]   -- some [100, 50, 25, 20]
#eval processAll [1, 0, 4, 5]   -- none

def filterValid (xs : List Nat) : List Nat :=
  xs.filterMap mayFail

#eval filterValid [1, 0, 2, 0, 4]  -- [100, 50, 25]
-- ANCHOR_END: combining_monads

-- ANCHOR: do_desugaring
def withBind (xs : List Nat) : Option Nat :=
  safeHead xs >>= fun x =>
  safeDivide 100 x >>= fun y =>
  pure (y + 1)

def withDoNotation (xs : List Nat) : Option Nat := do
  let x ← safeHead xs
  let y ← safeDivide 100 x
  return y + 1

#eval withBind [5]        -- some 21
#eval withDoNotation [5]  -- some 21

def mixedBindings : Option Nat := do
  let x ← some 10      -- monadic bind
  let y := x + 5       -- pure let
  let z ← some (y * 2) -- monadic bind
  return z

#eval mixedBindings  -- some 30
-- ANCHOR_END: do_desugaring

-- ANCHOR: do_mutable
def imperativeSum (xs : List Nat) : Nat := Id.run do
  let mut total := 0
  for x in xs do
    total := total + x
  return total

def functionalSum (xs : List Nat) : Nat :=
  xs.foldl (· + ·) 0

#eval imperativeSum [1, 2, 3, 4, 5]  -- 15
#eval functionalSum [1, 2, 3, 4, 5]  -- 15

def countValid (xs : List Nat) : IO Nat := do
  let mut count := 0
  for x in xs do
    if x > 0 then
      count := count + 1
      IO.println s!"Valid: {x}"
  return count
-- ANCHOR_END: do_mutable

-- ANCHOR: forin_class
structure CountDown where
  start : Nat

instance : ForIn Id CountDown Nat where
  forIn cd init f := do
    let mut acc := init
    let mut i := cd.start
    while i > 0 do
      match ← f i acc with
      | .done a  => return a  -- break
      | .yield a => acc := a  -- continue
      i := i - 1
    return acc

def sumCountDown (n : Nat) : Nat := Id.run do
  let mut total := 0
  for i in CountDown.mk n do
    total := total + i
  return total

#eval sumCountDown 5  -- 15 (5+4+3+2+1)
-- ANCHOR_END: forin_class

-- ANCHOR: form_class
def printAll (xs : List String) : IO Unit := do
  for x in xs do
    IO.println x

def sumWithIndex (arr : Array Nat) : Nat := Id.run do
  let mut total := 0
  for h : i in [0:arr.size] do
    total := total + arr[i]
  return total

#eval sumWithIndex #[10, 20, 30]  -- 60

def manualForIn (xs : List Nat) : Option Nat :=
  ForIn.forIn xs 0 fun x acc =>
    if x == 0 then some (.done acc)   -- early exit
    else some (.yield (acc + x))      -- continue

#eval manualForIn [1, 2, 3, 4]  -- some 10
#eval manualForIn [1, 2, 0, 4]  -- some 3 (stopped at 0)
-- ANCHOR_END: form_class

-- ANCHOR: iterators
def langs : List String := ["Lean", "Haskell", "Rust", "OCaml"]
def types : List String := ["theorem", "lazy", "systems", "modules"]

-- zip: pair elements from two collections
#eval langs.zip types
-- [("Lean", "theorem"), ("Haskell", "lazy"), ...]

-- map: transform each element
#eval langs.map String.toUpper
-- ["LEAN", "HASKELL", "RUST", "OCAML"]

-- filter: keep elements matching predicate
#eval langs.filter (·.startsWith "R")
-- ["Rust"]

-- take/drop: slice prefix or suffix
#eval langs.take 2
-- ["Lean", "Haskell"]
#eval langs.drop 2
-- ["Rust", "OCaml"]

-- filterMap: filter and transform in one pass
#eval ["42", "bad", "17"].filterMap String.toNat?
-- [42, 17]

-- find?: first element matching predicate
#eval langs.find? (·.length > 4)
-- some "Haskell"

-- any/all: check predicates
#eval langs.any (·.startsWith "L")  -- true
#eval langs.all (·.length > 3)      -- true

-- zipIdx: pair with indices
#eval ["a", "b", "c"].zipIdx
-- [("a", 0), ("b", 1), ("c", 2)]
-- ANCHOR_END: iterators

-- ANCHOR: folds
-- foldl: left fold, accumulator on the left
#eval [1, 2, 3, 4].foldl (· + ·) 0        -- 10
#eval ["a","b","c"].foldl (· ++ ·) ""     -- "abc"

-- foldr: right fold, accumulator on the right
#eval [1, 2, 3, 4].foldr (· + ·) 0        -- 10
#eval ["a","b","c"].foldr (· ++ ·) ""     -- "abc"

-- the difference: subtraction is not commutative
-- foldl f z [a,b,c] = f(f(f(z,a),b),c) = ((z⊕a)⊕b)⊕c
-- foldr f z [a,b,c] = f(a,f(b,f(c,z))) = a⊕(b⊕(c⊕z))
#eval ([1, 2, 3, 4] : List Int).foldl (· - ·) 0   -- -10: ((((0-1)-2)-3)-4)
#eval ([1, 2, 3, 4] : List Int).foldr (· - ·) 0   -- -2:  (1-(2-(3-(4-0))))

-- foldl builds left-to-right (tail recursive)
#eval [1, 2, 3].foldl (fun acc x => x :: acc) []  -- [3, 2, 1]

-- foldr builds right-to-left (preserves structure)
#eval [1, 2, 3].foldr (fun x acc => x :: acc) []  -- [1, 2, 3]

-- practical uses
#eval [10, 25, 8, 42, 3].foldl max 0              -- 42
#eval [2, 3, 4].foldl (· * ·) 1                   -- 24
#eval [1, 2, 3].foldl (fun acc x => acc + x * x) 0  -- 14
-- ANCHOR_END: folds

end ZeroToQED.Monads
