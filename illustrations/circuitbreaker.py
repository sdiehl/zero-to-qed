"""Circuit breaker state machine diagram."""

from pathlib import Path

from .core import (
    svg_viewbox,
    svg_bg,
    svg_rect,
    svg_text,
    DARK,
    BORDER,
    ARROW,
    TEXT,
    FONT_MONO,
    FONT_SANS,
)


def circuit_breaker_svg() -> str:
    width, height = 640, 320

    # State positions (horizontal layout: Closed - Open - HalfOpen)
    # Extra left margin to accommodate self-loop on Closed
    states = {
        "Closed": (150, 160),
        "Open": (320, 160),
        "HalfOpen": (490, 160),
    }

    # State colors (subtle left accent)
    state_colors = {
        "Closed": "#22c55e",   # green
        "Open": "#ef4444",     # red
        "HalfOpen": "#eab308", # amber
    }

    lines = [
        svg_viewbox(width, height),
        svg_bg(width, height),
        f'''  <defs>
    <marker id="arrow" markerWidth="8" markerHeight="6" refX="7" refY="3" orient="auto">
      <polygon points="0 0, 8 3, 0 6" fill="{ARROW}"/>
    </marker>
  </defs>''',
    ]

    # Draw curved transitions first (behind nodes)

    # Closed -> Open: straight arrow below
    cx, cy = states["Closed"]
    ox, oy = states["Open"]
    lines.append(
        f'<path d="M {cx + 55} {cy + 10} L {ox - 55} {oy + 10}" '
        f'stroke="{ARROW}" stroke-width="1.5" fill="none" marker-end="url(#arrow)"/>'
    )
    lines.append(svg_text((cx + ox) // 2, cy + 38, "failures &gt;= threshold",
                          size=10, anchor="middle", color=TEXT, font=FONT_SANS))

    # Open -> HalfOpen: straight arrow below
    hx, hy = states["HalfOpen"]
    lines.append(
        f'<path d="M {ox + 55} {oy + 10} L {hx - 55} {hy + 10}" '
        f'stroke="{ARROW}" stroke-width="1.5" fill="none" marker-end="url(#arrow)"/>'
    )
    lines.append(svg_text((ox + hx) // 2, oy + 38, "timeout elapsed",
                          size=10, anchor="middle", color=TEXT, font=FONT_SANS))

    # HalfOpen -> Closed: long curved arrow above (success path)
    lines.append(
        f'<path d="M {hx - 40} {hy - 30} Q {(cx + hx) // 2} {hy - 100} {cx + 40} {cy - 30}" '
        f'stroke="{ARROW}" stroke-width="1.5" fill="none" marker-end="url(#arrow)"/>'
    )
    lines.append(svg_text((cx + hx) // 2, hy - 85, "probe success",
                          size=10, anchor="middle", color=TEXT, font=FONT_SANS))

    # HalfOpen -> Open: curved arrow above (failure path)
    lines.append(
        f'<path d="M {hx - 50} {hy - 25} Q {(ox + hx) // 2} {hy - 70} {ox + 50} {oy - 25}" '
        f'stroke="{ARROW}" stroke-width="1.5" fill="none" marker-end="url(#arrow)"/>'
    )
    lines.append(svg_text((ox + hx) // 2, oy - 58, "probe failure",
                          size=10, anchor="middle", color=TEXT, font=FONT_SANS))

    # Self-loop on Closed (success resets) - left side
    lines.append(
        f'<path d="M {cx - 50} {cy - 15} C {cx - 90} {cy - 50} {cx - 90} {cy + 50} {cx - 50} {cy + 15}" '
        f'stroke="{ARROW}" stroke-width="1.5" fill="none" marker-end="url(#arrow)"/>'
    )
    lines.append(svg_text(cx - 95, cy, "success",
                          size=10, anchor="end", color=TEXT, font=FONT_SANS))

    # Self-loop on Open (tick waiting) - right side
    lines.append(
        f'<path d="M {ox + 50} {oy + 15} C {ox + 90} {oy + 50} {ox + 90} {oy - 50} {ox + 50} {oy - 15}" '
        f'stroke="{ARROW}" stroke-width="1.5" fill="none" marker-end="url(#arrow)"/>'
    )
    lines.append(svg_text(ox + 95, oy, "tick",
                          size=10, anchor="start", color=TEXT, font=FONT_SANS))

    # Draw state nodes
    node_w, node_h = 100, 50
    for name, (x, y) in states.items():
        rx = x - node_w // 2
        ry = y - node_h // 2
        color = state_colors[name]

        # Main box
        lines.append(svg_rect(rx, ry, node_w, node_h, fill="white", stroke=BORDER, rx=6))

        # Colored left accent bar
        lines.append(f'<rect x="{rx}" y="{ry}" width="4" height="{node_h}" fill="{color}" rx="2"/>')

        # State name
        lines.append(svg_text(x + 2, y + 5, name, size=13, anchor="middle",
                              color=DARK, weight="600", font=FONT_MONO))

    # Legend at bottom
    lines.append(svg_text(width // 2, height - 25, "Closed: failures &lt; threshold | Open: waiting for timeout | HalfOpen: testing recovery",
                          size=10, anchor="middle", color=TEXT, font=FONT_SANS))

    lines.append("</svg>")
    return "\n".join(lines)


def generate(output_dir: Path):
    output_dir.mkdir(parents=True, exist_ok=True)
    path = output_dir / "circuit_breaker.svg"
    path.write_text(circuit_breaker_svg())
    print(f"Generated {path}")
