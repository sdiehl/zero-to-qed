from pathlib import Path
from .core import svg_header, svg_bg, svg_arrow_marker, DARK, BORDER, ARROW, TEXT, FONT_MONO, FONT_SANS


def universe_svg() -> str:
    width, height = 400, 320
    box_w, box_h = 100, 36
    center_x = width // 2

    levels = [
        ("Prop", "Sort 0"),
        ("Type", "Sort 1"),
        ("Type 1", "Sort 2"),
        ("Type 2", "Sort 3"),
    ]

    lines = [
        svg_header(width, height),
        svg_bg(width, height),
        svg_arrow_marker(),
        f'''<style>
    .level {{ font-family: {FONT_MONO}; font-size: 14px; font-weight: bold; }}
    .sort {{ font-family: {FONT_SANS}; font-size: 11px; fill: {TEXT}; }}
    .label {{ font-family: {FONT_SANS}; font-size: 12px; fill: {TEXT}; }}
  </style>''',
    ]

    for i, (name, sort) in enumerate(levels):
        y = height - 50 - i * 70
        x = center_x - box_w // 2

        lines.append(
            f'<rect x="{x}" y="{y}" width="{box_w}" height="{box_h}" fill="none" stroke="{DARK}" stroke-width="1.5" rx="4"/>'
        )
        lines.append(
            f'<text x="{center_x}" y="{y + 23}" text-anchor="middle" fill="{DARK}" class="level">{name}</text>'
        )
        lines.append(f'<text x="{x + box_w + 12}" y="{y + 23}" class="sort">{sort}</text>')

        if i < len(levels) - 1:
            arrow_y1 = y
            arrow_y2 = y - 34
            lines.append(
                f'<line x1="{center_x}" y1="{arrow_y1}" x2="{center_x}" y2="{arrow_y2}" '
                f'stroke="{ARROW}" stroke-width="2" marker-end="url(#arrowhead)"/>'
            )

    lines.append(f'<text x="{center_x}" y="38" text-anchor="middle" class="label">⋮</text>')
    lines.append(f'<text x="30" y="{height - 35}" class="label">Propositions</text>')
    lines.append(f'<text x="30" y="{height - 105}" class="label">Data types</text>')

    lines.append("</svg>")
    return "\n".join(lines)


def algebra_svg() -> str:
    width, height = 500, 380

    structures = {
        "Semigroup": (100, 320),
        "Monoid": (100, 240),
        "Group": (100, 160),
        "CommGroup": (50, 80),
        "Ring": (200, 80),
        "CommRing": (125, 20),
        "Field": (275, 20),
        "AddMonoid": (350, 240),
        "AddGroup": (350, 160),
        "Module": (400, 80),
    }

    edges = [
        ("Semigroup", "Monoid"),
        ("Monoid", "Group"),
        ("Group", "CommGroup"),
        ("Group", "Ring"),
        ("CommGroup", "CommRing"),
        ("Ring", "CommRing"),
        ("Ring", "Field"),
        ("CommRing", "Field"),
        ("AddMonoid", "AddGroup"),
        ("AddGroup", "Ring"),
        ("AddGroup", "Module"),
    ]

    lines = [
        svg_header(width, height),
        svg_bg(width, height),
        f'''<defs>
    <marker id="arr" markerWidth="8" markerHeight="6" refX="7" refY="3" orient="auto">
      <polygon points="0 0, 8 3, 0 6" fill="{ARROW}"/>
    </marker>
  </defs>''',
        f'<style>.struct {{ font-family: {FONT_MONO}; font-size: 11px; font-weight: 500; }}</style>',
    ]

    for src, dst in edges:
        x1, y1 = structures[src]
        x2, y2 = structures[dst]
        dx, dy = x2 - x1, y2 - y1
        dist = (dx**2 + dy**2) ** 0.5
        if dist > 0:
            ux, uy = dx / dist, dy / dist
            x1 += ux * 35
            y1 += uy * 12
            x2 -= ux * 35
            y2 -= uy * 12
        lines.append(
            f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" '
            f'stroke="{BORDER}" stroke-width="1.5" marker-end="url(#arr)"/>'
        )

    for name, (x, y) in structures.items():
        box_w = len(name) * 8 + 16
        box_h = 24
        rx = x - box_w // 2
        ry = y - box_h // 2
        lines.append(f'<rect x="{rx}" y="{ry}" width="{box_w}" height="{box_h}" fill="none" stroke="{DARK}" stroke-width="1.5" rx="4"/>')
        lines.append(f'<text x="{x}" y="{y + 4}" text-anchor="middle" fill="{DARK}" class="struct">{name}</text>')

    lines.append("</svg>")
    return "\n".join(lines)


def generate(output_dir: Path):
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / "universe_hierarchy.svg").write_text(universe_svg())
    (output_dir / "algebra_hierarchy.svg").write_text(algebra_svg())
    print(f"Generated hierarchy SVGs in {output_dir}")
