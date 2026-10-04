-- ANCHOR: grammar
inductive Grammar where
  | char : Char → Grammar
  | seq : Grammar → Grammar → Grammar
  | alt : Grammar → Grammar → Grammar
  | many : Grammar → Grammar
  | eps : Grammar

inductive Matches : Grammar → List Char → Prop where
  | char {c} : Matches (.char c) [c]
  | eps : Matches .eps []
  | seq {g₁ g₂ s₁ s₂} : Matches g₁ s₁ → Matches g₂ s₂ → Matches (.seq g₁ g₂) (s₁ ++ s₂)
  | altL {g₁ g₂ s} : Matches g₁ s → Matches (.alt g₁ g₂) s
  | altR {g₁ g₂ s} : Matches g₂ s → Matches (.alt g₁ g₂) s
  | manyNil {g} : Matches (.many g) []
  | manyCons {g s₁ s₂} : Matches g s₁ → Matches (.many g) s₂ → Matches (.many g) (s₁ ++ s₂)
-- ANCHOR_END: grammar

-- ANCHOR: parser
structure ParseResult (g : Grammar) (input : List Char) where
  consumed : List Char
  rest : List Char
  proof : Matches g consumed
  split : consumed ++ rest = input

abbrev Parser (g : Grammar) := (input : List Char) → Option (ParseResult g input)
-- ANCHOR_END: parser

-- ANCHOR: combinators
def pchar (c : Char) : Parser (.char c) := fun
  | x :: xs => if h : x = c then some ⟨[c], xs, .char, by simp [h]⟩ else none
  | [] => none

variable {g₁ g₂ g : Grammar}

def pseq (p₁ : Parser g₁) (p₂ : Parser g₂) : Parser (.seq g₁ g₂) := fun input =>
  p₁ input |>.bind fun ⟨s₁, r, pf₁, hs₁⟩ => p₂ r |>.map fun ⟨s₂, r', pf₂, hs₂⟩ =>
    ⟨s₁ ++ s₂, r', .seq pf₁ pf₂, by rw [List.append_assoc, hs₂, hs₁]⟩

def palt (p₁ : Parser g₁) (p₂ : Parser g₂) : Parser (.alt g₁ g₂) := fun input =>
  (p₁ input |>.map fun ⟨s, r, pf, hs⟩ => ⟨s, r, .altL pf, hs⟩) <|>
  (p₂ input |>.map fun ⟨s, r, pf, hs⟩ => ⟨s, r, .altR pf, hs⟩)

def pmany (p : Parser g) (input : List Char) : Option (ParseResult (.many g) input) :=
  match p input with
  | none => some ⟨[], input, .manyNil, rfl⟩
  | some ⟨s₁, r, pf₁, hs₁⟩ =>
    if h : s₁ = [] then some ⟨[], input, .manyNil, rfl⟩
    else (pmany p r).map fun ⟨s₂, r', pf₂, hs₂⟩ =>
      ⟨s₁ ++ s₂, r', .manyCons pf₁ pf₂, by rw [List.append_assoc, hs₂, hs₁]⟩
termination_by input.length
decreasing_by
  have hlen := congrArg List.length hs₁
  simp only [List.length_append] at hlen
  have hpos : 0 < s₁.length := List.length_pos_iff.mpr h
  omega

infixl:60 " *> " => pseq
infixl:50 " <+> " => palt
postfix:90 "⁺" => pmany
-- ANCHOR_END: combinators

-- ANCHOR: soundness
theorem soundness (p : Parser g) (input : List Char) (r : ParseResult g input) :
    p input = some r → Matches g r.consumed ∧ r.consumed ++ r.rest = input :=
  fun _ => ⟨r.proof, r.split⟩
-- ANCHOR_END: soundness

-- ANCHOR: example
def letter := palt (palt (palt (pchar 'a') (pchar 'b')) (pchar 'x')) (pchar 'y')
def digit := palt (palt (palt (pchar '0') (pchar '1')) (pchar '2')) (pchar '3')
def ident := pseq letter (pmany (palt letter digit))
-- ANCHOR_END: example

def run {g : Grammar} (p : Parser g) (s : String) : Option String :=
  (p s.toList).map fun r => String.ofList r.consumed

-- A parser cannot fabricate a character from empty input.
example (c : Char) (p : Parser (.char c)) : p [] = none := by
  cases h : p [] with
  | none => rfl
  | some r =>
    obtain ⟨consumed, rest, proof, split⟩ := r
    cases proof
    simp at split

#guard run (pchar 'a') "" == none
#guard run (pchar 'a' *> pchar 'b') "abc" == some "ab"
#guard run ((pchar 'a')⁺) "aaab" == some "aaa"
#guard run ident "xy12" == some "xy12"
-- Repeating a nullable parser terminates without consuming input.
#guard run (pmany (g := .eps) (fun input => some ⟨[], input, .eps, rfl⟩)) "abc" == some ""

def main : IO Unit := do
  IO.println s!"char 'a' on \"abc\":  {run (pchar 'a') "abc"}"
  IO.println s!"a *> b on \"abc\":    {run (pchar 'a' *> pchar 'b') "abc"}"
  IO.println s!"a <+> b on \"bx\":    {run (pchar 'a' <+> pchar 'b') "bx"}"
  IO.println s!"a+ on \"aaab\":       {run ((pchar 'a')⁺) "aaab"}"
  IO.println s!"ident on \"xy12\":    {run ident "xy12"}"
