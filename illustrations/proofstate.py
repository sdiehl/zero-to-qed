"""
Proof state evolution diagrams showing how tactics transform goals step by step.
"""

from dataclasses import dataclass, field
from pathlib import Path
from .core import (
    svg_viewbox,
    svg_bg,
    svg_text,
    svg_line,
    svg_rect,
    DARK,
    BORDER,
    ARROW,
    ACCENT,
    TEXT,
    HIGHLIGHT_NEW,
    HIGHLIGHT_USED,
    FONT_MONO,
)


@dataclass
class Hyp:
    name: str
    type: str
    new: bool = False
    used: bool = False


@dataclass
class ProofState:
    ctx: list = field(default_factory=list)
    goal: str = ""
    label: str = ""


@dataclass
class Step:
    tactic: str
    state: ProofState


def render_state_box(x: int, y: int, state: ProofState, width: int = 200) -> tuple:
    """Render a single proof state box. Returns (svg_parts, height)."""
    parts = []
    padding = 8
    line_h = 18

    # Calculate height based on content
    ctx_lines = max(len(state.ctx), 1)
    content_h = ctx_lines * line_h + line_h + 10  # context + goal + spacing
    box_h = content_h + padding * 2

    # Box background
    parts.append(svg_rect(x, y, width, box_h, fill="#fafafa", stroke=BORDER, rx=4))

    cy = y + padding

    # Context
    if state.ctx:
        for h in state.ctx:
            clr = HIGHLIGHT_NEW if h.new else (HIGHLIGHT_USED if h.used else DARK)
            wt = "600" if (h.new or h.used) else "normal"
            parts.append(svg_text(x + padding, cy + 13, f"{h.name} : {h.type}",
                                  size=11, color=clr, weight=wt))
            cy += line_h
    else:
        parts.append(svg_text(x + padding, cy + 13, "(empty context)",
                              size=10, color=TEXT, style="italic"))
        cy += line_h

    # Separator line
    cy += 2
    parts.append(svg_line(x + padding, cy, x + width - padding, cy, BORDER, 1))
    cy += 6

    # Goal
    if state.goal:
        parts.append(svg_text(x + padding, cy + 13, f"⊢ {state.goal}",
                              size=11, color=DARK))
    else:
        parts.append(svg_text(x + padding, cy + 13, "⊢ goals accomplished",
                              size=10, color=ACCENT, style="italic"))

    return "\n".join(parts), box_h


def render_arrow(x1: int, y: int, x2: int, tactic: str) -> str:
    """Render a horizontal arrow with tactic label."""
    parts = []
    mid_y = y

    # Arrow line
    parts.append(svg_line(x1, mid_y, x2 - 8, mid_y, ARROW, 1.5))

    # Arrowhead
    parts.append(f'<polygon points="{x2-8},{mid_y-4} {x2},{mid_y} {x2-8},{mid_y+4}" fill="{ARROW}"/>')

    # Tactic label above arrow
    mid_x = (x1 + x2) // 2
    parts.append(svg_text(mid_x, mid_y - 8, tactic, size=10, anchor="middle",
                          color=DARK, weight="600"))

    return "\n".join(parts)


def render_evolution(steps: list, title: str = "") -> str:
    """Render a horizontal sequence of proof states connected by arrows."""
    box_width = 180
    arrow_width = 80
    padding = 20

    # Calculate total width
    n_boxes = len(steps)
    total_width = n_boxes * box_width + (n_boxes - 1) * arrow_width + padding * 2

    # First pass: calculate max height
    max_box_h = 0
    for step in steps:
        _, h = render_state_box(0, 0, step.state, box_width)
        max_box_h = max(max_box_h, h)

    title_h = 30 if title else 0
    total_height = title_h + max_box_h + padding * 2

    svg = [svg_viewbox(total_width, total_height), svg_bg(total_width, total_height)]

    # Title
    if title:
        svg.append(svg_text(total_width // 2, 20, title, size=12, anchor="middle",
                            color=DARK, weight="600"))

    x = padding
    y = title_h + padding

    for i, step in enumerate(steps):
        # Draw state box
        box_svg, box_h = render_state_box(x, y, step.state, box_width)
        svg.append(box_svg)

        # Draw arrow to next state (if not last)
        if i < len(steps) - 1:
            arrow_x1 = x + box_width + 5
            arrow_x2 = arrow_x1 + arrow_width - 10
            arrow_y = y + max_box_h // 2
            svg.append(render_arrow(arrow_x1, arrow_y, arrow_x2, steps[i + 1].tactic))

        x += box_width + arrow_width

    svg.append("</svg>")
    return "\n".join(svg)


def render_vertical_evolution(steps: list, title: str = "") -> str:
    """Render a vertical sequence of proof states connected by arrows."""
    box_width = 260
    arrow_height = 50
    padding = 16

    # First pass: calculate heights
    box_heights = []
    for step in steps:
        _, h = render_state_box(0, 0, step.state, box_width)
        box_heights.append(h)

    title_h = 28 if title else 0
    total_height = title_h + sum(box_heights) + (len(steps) - 1) * arrow_height + padding * 2
    total_width = box_width + padding * 2

    svg = [svg_viewbox(total_width, total_height), svg_bg(total_width, total_height)]

    # Title
    if title:
        svg.append(svg_text(total_width // 2, 20, title, size=12, anchor="middle",
                            color=DARK, weight="600"))

    x = padding
    y = title_h + padding

    for i, step in enumerate(steps):
        # Draw state box
        box_svg, box_h = render_state_box(x, y, step.state, box_width)
        svg.append(box_svg)
        y += box_h

        # Draw arrow to next state (if not last)
        if i < len(steps) - 1:
            mid_x = x + box_width // 2
            arrow_y1 = y + 5
            arrow_y2 = y + arrow_height - 10

            # Arrow line
            svg.append(svg_line(mid_x, arrow_y1, mid_x, arrow_y2, ARROW, 1.5))
            # Arrowhead
            svg.append(f'<polygon points="{mid_x-4},{arrow_y2} {mid_x+4},{arrow_y2} {mid_x},{arrow_y2+6}" fill="{ARROW}"/>')
            # Tactic label
            svg.append(svg_text(mid_x + 10, (arrow_y1 + arrow_y2) // 2 + 4,
                                steps[i + 1].tactic, size=10, color=DARK, weight="600"))
            y += arrow_height

    svg.append("</svg>")
    return "\n".join(svg)


# Example proof evolutions
EVOLUTIONS = {
    "intro_chain": (
        "intro h, intro _, exact h",
        [
            Step("", ProofState([], "P → Q → P")),
            Step("intro h", ProofState([Hyp("h", "P", new=True)], "Q → P")),
            Step("intro _", ProofState([Hyp("h", "P"), Hyp("_", "Q", new=True)], "P")),
            Step("exact h", ProofState([Hyp("h", "P", used=True), Hyp("_", "Q")], "")),
        ]
    ),
    "induction_nat": (
        "Proof by induction on n",
        [
            Step("", ProofState([Hyp("n", "Nat")], "P n")),
            Step("induction n", ProofState([], "P 0 ∧ (∀k, P k → P (k+1))")),
        ]
    ),
    "constructor_split": (
        "constructor splits conjunction",
        [
            Step("", ProofState([Hyp("hp", "P"), Hyp("hq", "Q")], "P ∧ Q")),
            Step("constructor", ProofState([Hyp("hp", "P"), Hyp("hq", "Q")], "P")),
        ]
    ),
    "apply_chain": (
        "apply works backwards",
        [
            Step("", ProofState([Hyp("h₁", "P → Q"), Hyp("h₂", "Q → R"), Hyp("hp", "P")], "R")),
            Step("apply h₂", ProofState([Hyp("h₁", "P → Q"), Hyp("h₂", "Q → R", used=True), Hyp("hp", "P")], "Q")),
            Step("apply h₁", ProofState([Hyp("h₁", "P → Q", used=True), Hyp("h₂", "Q → R"), Hyp("hp", "P")], "P")),
            Step("exact hp", ProofState([Hyp("h₁", "P → Q"), Hyp("h₂", "Q → R"), Hyp("hp", "P", used=True)], "")),
        ]
    ),
    "cases_or": (
        "cases splits disjunction",
        [
            Step("", ProofState([Hyp("h", "P ∨ Q")], "R")),
            Step("cases h", ProofState([Hyp("hp", "P", new=True)], "R")),
        ]
    ),
}


def generate(output_dir: Path):
    output_dir.mkdir(parents=True, exist_ok=True)

    for name, (title, steps) in EVOLUTIONS.items():
        # Generate vertical version (better for narrow displays)
        svg = render_vertical_evolution(steps, title)
        (output_dir / f"proof_evolution_{name}.svg").write_text(svg)

    print(f"Generated {len(EVOLUTIONS)} proof evolution diagrams in {output_dir}")
