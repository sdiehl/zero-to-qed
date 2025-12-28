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
structure ParseResult (g : Grammar) where
  consumed : List Char
  rest : List Char
  proof : Matches g consumed

abbrev Parser (g : Grammar) := List Char → Option (ParseResult g)
-- ANCHOR_END: parser

-- ANCHOR: combinators
def pchar (c : Char) : Parser (.char c) := fun
  | x :: xs => if h : x = c then some ⟨[c], xs, h ▸ .char⟩ else none
  | [] => none

variable {g₁ g₂ g : Grammar}

def pseq (p₁ : Parser g₁) (p₂ : Parser g₂) : Parser (.seq g₁ g₂) := fun input =>
  p₁ input |>.bind fun ⟨s₁, r, pf₁⟩ => p₂ r |>.map fun ⟨s₂, r', pf₂⟩ => ⟨s₁ ++ s₂, r', .seq pf₁ pf₂⟩

def palt (p₁ : Parser g₁) (p₂ : Parser g₂) : Parser (.alt g₁ g₂) := fun input =>
  (p₁ input |>.map fun ⟨s, r, pf⟩ => ⟨s, r, .altL pf⟩) <|>
  (p₂ input |>.map fun ⟨s, r, pf⟩ => ⟨s, r, .altR pf⟩)

partial def pmany (p : Parser g) : Parser (.many g) := fun input =>
  match p input with
  | none => some ⟨[], input, .manyNil⟩
  | some ⟨s₁, r, pf₁⟩ =>
    if s₁.isEmpty then some ⟨[], input, .manyNil⟩
    else (pmany p r).map fun ⟨s₂, r', pf₂⟩ => ⟨s₁ ++ s₂, r', .manyCons pf₁ pf₂⟩

infixl:60 " *> " => pseq
infixl:50 " <+> " => palt
postfix:90 "⁺" => pmany
-- ANCHOR_END: combinators

-- ANCHOR: soundness
theorem soundness (p : Parser g) (input : List Char) (r : ParseResult g) :
    p input = some r → Matches g r.consumed := fun _ => r.proof
-- ANCHOR_END: soundness

-- ANCHOR: example
def letter := palt (palt (palt (pchar 'a') (pchar 'b')) (pchar 'x')) (pchar 'y')
def digit := palt (palt (palt (pchar '0') (pchar '1')) (pchar '2')) (pchar '3')
def ident := pseq letter (pmany (palt letter digit))
-- ANCHOR_END: example

def run {g : Grammar} (p : Parser g) (s : String) : Option String :=
  (p s.toList).map fun r => String.mk r.consumed

def main : IO Unit := do
  IO.println "=== Proof-Carrying Parser Combinators ==="
  IO.println s!"char 'a' on abc: {run (pchar 'a') "abc"}"
  IO.println s!"a *> b on abc:   {run (pchar 'a' *> pchar 'b') "abc"}"
  IO.println s!"a <+> b on bx:   {run (pchar 'a' <+> pchar 'b') "bx"}"
  IO.println s!"a+ on aaab:      {run ((pchar 'a')⁺) "aaab"}"
  IO.println s!"ident on xy12:   {run ident "xy12"}"
  IO.println ""
  IO.println "Every ParseResult carries `proof : Matches g consumed`"
  IO.println "Invalid parses are impossible by construction."
