from pathlib import Path
from .core import DARK, FONT_SERIF

WIDTH = 340
HEIGHT = 220

def generate_lambda_cube(output_dir: Path) -> None:
    origin = (80, 170)
    x_step = (100, 0)
    y_step = (0, -80)
    z_step = (60, -40)

    def vertex(p, t, d):
        return (
            origin[0] + p * x_step[0] + t * y_step[0] + d * z_step[0],
            origin[1] + p * x_step[1] + t * y_step[1] + d * z_step[1]
        )

    v = {
        "stlc": vertex(0, 0, 0),
        "l2":   vertex(1, 0, 0),
        "lw":   vertex(0, 1, 0),
        "lw_":  vertex(1, 1, 0),
        "lP":   vertex(0, 0, 1),
        "lP2":  vertex(1, 0, 1),
        "lPw":  vertex(0, 1, 1),
        "lC":   vertex(1, 1, 1),
    }

    labels = {
        "stlc": ("λ→", -28, 5),
        "l2":   ("λ2", 8, 5),
        "lw":   ("λω", -28, 5),
        "lw_":  ("λω̲", 8, 5),
        "lP":   ("λP", -28, 5),
        "lP2":  ("λP2", 8, 5),
        "lPw":  ("λPω̲", -38, 5),
        "lC":   ("λC", 8, 5),
    }

    front = [("stlc", "l2"), ("stlc", "lw"), ("l2", "lw_"), ("lw", "lw_")]
    back = [("lP", "lP2"), ("lP", "lPw"), ("lP2", "lC"), ("lPw", "lC")]
    depth = [("stlc", "lP"), ("l2", "lP2"), ("lw", "lPw"), ("lw_", "lC")]

    svg = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{WIDTH}" height="{HEIGHT}">',
        f'<rect width="{WIDTH}" height="{HEIGHT}" fill="white"/>',
    ]

    for a, b in back:
        svg.append(f'<line x1="{v[a][0]}" y1="{v[a][1]}" x2="{v[b][0]}" y2="{v[b][1]}" stroke="#cbd5e0" stroke-width="1.5"/>')

    for a, b in depth:
        svg.append(f'<line x1="{v[a][0]}" y1="{v[a][1]}" x2="{v[b][0]}" y2="{v[b][1]}" stroke="#cbd5e0" stroke-width="1.5" stroke-dasharray="5,4"/>')

    for a, b in front:
        svg.append(f'<line x1="{v[a][0]}" y1="{v[a][1]}" x2="{v[b][0]}" y2="{v[b][1]}" stroke="#4a5568" stroke-width="1.5"/>')

    for name, (x, y) in v.items():
        fill = "#4299e1" if name == "lC" else DARK
        r = 5 if name == "lC" else 4
        svg.append(f'<circle cx="{x}" cy="{y}" r="{r}" fill="{fill}"/>')

    for name, (text, dx, dy) in labels.items():
        x, y = v[name]
        color = "#2b6cb0" if name == "lC" else DARK
        svg.append(f'<text x="{x + dx}" y="{y + dy}" font-family="{FONT_SERIF}" font-size="13" fill="{color}" font-style="italic">{text}</text>')

    svg.append("</svg>")
    (output_dir / "lambda_cube.svg").write_text("\n".join(svg))
    print(f"Generated lambda cube in {output_dir}")
