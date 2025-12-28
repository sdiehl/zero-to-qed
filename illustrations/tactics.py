from dataclasses import dataclass, field
from pathlib import Path
from .core import svg_viewbox, svg_bg, svg_text, svg_line, DARK, BORDER, ARROW, ACCENT, TEXT, HIGHLIGHT_NEW, HIGHLIGHT_USED


@dataclass
class Hyp:
    name: str
    type: str
    new: bool = False
    used: bool = False


@dataclass
class State:
    ctx: list = field(default_factory=list)
    goals: list = field(default_factory=list)
    term: str = "?"


@dataclass
class Tactic:
    name: str
    before: State
    after: State


TACTICS = [
    Tactic("intro h",
           State([], ["P → Q"]),
           State([Hyp("h", "P", new=True)], ["Q"], "λ h ⇒ ?")),
    Tactic("apply h",
           State([Hyp("h", "P → Q")], ["Q"]),
           State([Hyp("h", "P → Q", used=True)], ["P"], "h ?")),
    Tactic("exact h",
           State([Hyp("h", "P")], ["P"]),
           State([Hyp("h", "P", used=True)], [], "h")),
    Tactic("cases h",
           State([Hyp("h", "P ∨ Q")], ["R"]),
           State([Hyp("h", "P ∨ Q", used=True)], ["P → R", "Q → R"], "h.elim ? ?")),
    Tactic("constructor",
           State([], ["P ∧ Q"]),
           State([], ["P", "Q"], "⟨?, ?⟩")),
    Tactic("left",
           State([], ["P ∨ Q"]),
           State([], ["P"], "Or.inl ?")),
    Tactic("right",
           State([], ["P ∨ Q"]),
           State([], ["Q"], "Or.inr ?")),
    Tactic("use x",
           State([], ["∃ n, P n"]),
           State([], ["P x"], "⟨x, ?⟩")),
    Tactic("obtain ⟨w, hw⟩ := h",
           State([Hyp("h", "∃ n, P n")], ["Q"]),
           State([Hyp("w", "α", new=True), Hyp("hw", "P w", new=True)], ["Q"], "let ⟨w, hw⟩ := h; ?")),
    Tactic("have h : P := proof",
           State([], ["Q"]),
           State([Hyp("h", "P", new=True)], ["Q"], "let h := proof; ?")),
    Tactic("induction n",
           State([Hyp("n", "ℕ")], ["P n"]),
           State([Hyp("n", "ℕ", used=True)], ["P 0", "∀ k, P k → P (k+1)"], "Nat.rec ? ?")),
    Tactic("rw [h]",
           State([Hyp("h", "a = b")], ["P a"]),
           State([Hyp("h", "a = b", used=True)], ["P b"], "h ▸ ?")),
    Tactic("by_contra h",
           State([], ["P"]),
           State([Hyp("h", "¬P", new=True)], ["False"], "byContradiction ?")),
    Tactic("exfalso",
           State([], ["P"]),
           State([], ["False"], "False.elim ?")),
    Tactic("simp",
           State([], ["a + 0 = a"]),
           State([], ["a = a"], "by simp")),
    Tactic("rfl",
           State([], ["a = a"]),
           State([], [], "rfl")),
    Tactic("assumption",
           State([Hyp("h", "P")], ["P"]),
           State([Hyp("h", "P", used=True)], [], "h")),
    Tactic("contradiction",
           State([Hyp("h", "P"), Hyp("h'", "¬P")], ["Q"]),
           State([Hyp("h", "P", used=True), Hyp("h'", "¬P", used=True)], [], "absurd h h'")),
    Tactic("symm",
           State([], ["a = b"]),
           State([], ["b = a"], "Eq.symm ?")),
    Tactic("trans b",
           State([], ["a = c"]),
           State([], ["a = b", "b = c"], "Eq.trans ? ?")),
    Tactic("specialize h a",
           State([Hyp("h", "∀ x, P x")], ["Q"]),
           State([Hyp("h", "P a", new=True)], ["Q"], "?")),
    Tactic("revert h",
           State([Hyp("h", "P")], ["Q"]),
           State([], ["P → Q"], "λ h ⇒ ?")),
    Tactic("push_neg",
           State([], ["¬∀ x, P x"]),
           State([], ["∃ x, ¬P x"], "?")),
    Tactic("congr",
           State([], ["f a = f b"]),
           State([], ["a = b"], "congrArg f ?")),
    Tactic("ext x",
           State([], ["f = g"]),
           State([Hyp("x", "α", new=True)], ["f x = g x"], "funext (λ x ⇒ ?)")),
    Tactic("subst h",
           State([Hyp("x", "α"), Hyp("h", "x = e")], ["P x"]),
           State([Hyp("h", "x = e", used=True)], ["P e"], "h ▸ ?")),
]


def render_state(x: int, y: int, state: State, width: int) -> tuple:
    parts = []
    cy = y
    label_x, value_x, line_h = x + 12, x + 70, 20

    parts.append(svg_text(label_x, cy + 14, "Context:", size=10, color=TEXT))
    if state.ctx:
        for h in state.ctx:
            clr = HIGHLIGHT_NEW if h.new else (HIGHLIGHT_USED if h.used else DARK)
            wt = "600" if (h.new or h.used) else "normal"
            parts.append(svg_text(value_x, cy + 14, f"{h.name} : {h.type}", color=clr, weight=wt))
            cy += line_h
    else:
        parts.append(svg_text(value_x, cy + 14, "—", color=TEXT))
        cy += line_h

    cy += 4
    parts.append(svg_text(label_x, cy + 14, "Goal:", size=10, color=TEXT))
    if state.goals:
        for i, g in enumerate(state.goals):
            prefix = "" if i == 0 else "     "
            parts.append(svg_text(value_x, cy + 14, f"{prefix}⊢ {g}", color=DARK))
            cy += line_h
    else:
        parts.append(svg_text(value_x, cy + 14, "✓ goals accomplished", color=ACCENT, style="italic"))
        cy += line_h

    return "\n".join(parts), cy


def render_tactic(t: Tactic) -> str:
    width, padding = 340, 16
    before_h = max(len(t.before.ctx), 1) * 20 + max(len(t.before.goals), 1) * 20 + 8
    after_h = max(len(t.after.ctx), 1) * 20 + max(len(t.after.goals), 1) * 20 + 8
    fold_h, term_h = 36, 24
    total_h = padding + before_h + fold_h + after_h + term_h + padding

    svg = [svg_viewbox(width, total_h), svg_bg(width, total_h)]

    y = padding
    before_svg, y = render_state(0, y, t.before, width)
    svg.append(before_svg)
    y += 8

    fold_y = y + fold_h / 2
    svg.append(svg_line(padding, fold_y, width * 0.32, fold_y, BORDER, 1.5))
    svg.append(svg_text(width / 2, fold_y + 4, t.name, size=11, anchor="middle", color=DARK, weight="600"))
    svg.append(svg_line(width * 0.68, fold_y, width - padding, fold_y, BORDER, 1.5))

    arrow_x = width / 2
    svg.append(svg_line(arrow_x, fold_y + 8, arrow_x, fold_y + 16, ARROW, 1.5))
    svg.append(f'<polygon points="{arrow_x-4},{fold_y+14} {arrow_x+4},{fold_y+14} {arrow_x},{fold_y+20}" fill="{ARROW}"/>')
    y += fold_h

    after_svg, y = render_state(0, y, t.after, width)
    svg.append(after_svg)
    y += 8

    svg.append(svg_text(width / 2, y + 12, f"term: {t.after.term}", size=9, anchor="middle", color=TEXT, style="italic"))
    svg.append("</svg>")
    return "\n".join(svg)


def generate(output_dir: Path):
    output_dir.mkdir(parents=True, exist_ok=True)
    for t in TACTICS:
        name = t.name.split()[0].replace("⟨", "").replace("⟩", "").replace(":=", "")
        (output_dir / f"tactic_{name}.svg").write_text(render_tactic(t))
    print(f"Generated {len(TACTICS)} tactic diagrams in {output_dir}")
