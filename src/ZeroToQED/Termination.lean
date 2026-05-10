/-!
# Termination and Well-Founded Recursion

How Lean checks that recursive functions terminate, and what to do when
the automatic checker cannot see why.
-/

namespace ZeroToQED.Termination

-- ANCHOR: structural_review
-- Structural recursion: each recursive call peels off a constructor.
-- Lean accepts these without any annotation.
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

#eval factorial 6           -- 720
#eval listSum [1, 2, 3, 4]  -- 10
-- ANCHOR_END: structural_review

-- ANCHOR: termination_by_basic
-- When the decreasing argument is not structural, name a measure with
-- termination_by. Lean synthesizes the proof from Nat's well-founded order.
def halve (n : Nat) : Nat :=
  if n < 2 then 0
  else 1 + halve (n / 2)
termination_by n

#eval halve 1024  -- 10
-- ANCHOR_END: termination_by_basic

-- ANCHOR: gcd_decreasing
-- The decreasing argument is a computed value. Euclidean GCD recurses on
-- the remainder, which is strictly less than `b` only when `b > 0`. The
-- compiler needs help seeing this, so we provide the proof in decreasing_by.
def gcdEuclid (a b : Nat) : Nat :=
  if _h : b = 0 then a
  else gcdEuclid b (a % b)
termination_by b
decreasing_by
  exact Nat.mod_lt a (Nat.pos_of_ne_zero _h)

#eval gcdEuclid 48 18  -- 6
#eval gcdEuclid 17 13  -- 1
-- ANCHOR_END: gcd_decreasing

-- ANCHOR: lex_termination
-- Multiple arguments: termination_by produces a lexicographic measure.
-- Ackermann decreases on the pair (m, n): either m drops, or m stays and
-- n drops with the inner call.
def ackermann : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ackermann m 1
  | m + 1, n + 1 => ackermann m (ackermann (m + 1) n)
termination_by m n => (m, n)

#eval ackermann 2 3  -- 9
#eval ackermann 3 3  -- 61
-- ANCHOR_END: lex_termination

-- ANCHOR: have_termination
-- A `have` clause inside the function body can discharge the termination
-- goal directly. The compiler scans your local hypotheses when synthesizing
-- the proof, so naming the inequality is often enough.
def digits (n : Nat) : List Nat :=
  if h : n = 0 then []
  else
    have : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)
    digits (n / 10) ++ [n % 10]
termination_by n

#eval digits 12345  -- [1, 2, 3, 4, 5]
-- ANCHOR_END: have_termination

-- ANCHOR: wellfounded_fix
-- Under the hood, every well-founded recursion compiles to WellFounded.fix.
-- You can call it directly when you want explicit control or are studying
-- how the elaborator works.
def countdown (n : Nat) : List Nat :=
  (Nat.lt_wfRel.wf).fix (C := fun _ => List Nat)
    (fun n rec =>
      if h : n = 0 then []
      else
        have : n - 1 < n := Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.one_pos
        n :: rec (n - 1) this)
    n

#eval countdown 5  -- [5, 4, 3, 2, 1]
-- ANCHOR_END: wellfounded_fix

-- ANCHOR: partial_escape
-- When termination is genuinely hard to bound, partial skips the proof.
-- The function still compiles and runs, but it cannot appear in proofs.
partial def fixpoint {α : Type} [BEq α] (f : α → α) (x : α) : α :=
  let y := f x
  if y == x then x else fixpoint f y

#eval fixpoint (fun n : Nat => n / 2) 100  -- 0

-- The trade-off: partial functions are opaque to the kernel, so you cannot
-- unfold them in a proof. Use them for prototyping or genuinely partial
-- algorithms (interpreters, network loops, anything where termination
-- depends on external state).
-- ANCHOR_END: partial_escape

-- ANCHOR: fuel_pattern
-- A common pattern when you cannot bound the recursion: pass an explicit
-- fuel parameter that strictly decreases. The fuel is the termination
-- measure. The Collatz sequence is the canonical example because no one
-- knows how to bound the actual descent.
def collatzWithFuel (fuel n : Nat) : List Nat :=
  match fuel with
  | 0 => [n]
  | fuel + 1 =>
    if n ≤ 1 then [n]
    else if n % 2 == 0 then
      n :: collatzWithFuel fuel (n / 2)
    else
      n :: collatzWithFuel fuel (3 * n + 1)

#eval (collatzWithFuel 200 27).length  -- 112
-- ANCHOR_END: fuel_pattern

end ZeroToQED.Termination
