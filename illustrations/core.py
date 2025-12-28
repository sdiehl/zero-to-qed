import tomllib
from dataclasses import dataclass
from pathlib import Path

_styles_path = Path(__file__).parent.parent / "styles.toml"
with open(_styles_path, "rb") as f:
    _styles = tomllib.load(f)

DARK = _styles["colors"]["dark"]
LIGHT = _styles["colors"]["light"]
BORDER = _styles["colors"]["border"]
ARROW = _styles["colors"]["arrow"]
ACCENT = _styles["colors"]["accent"]
TEXT = _styles["colors"]["text"]
HIGHLIGHT_NEW = _styles["colors"]["highlight-new"]
HIGHLIGHT_USED = _styles["colors"]["highlight-used"]

FONT_MONO = _styles["fonts"]["mono"]
FONT_SANS = _styles["fonts"]["sans"]
FONT_SERIF = _styles["fonts"]["serif"]


def svg_header(width: int, height: int) -> str:
    return f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}">'


def svg_viewbox(width: int, height: int) -> str:
    return f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}">'


def svg_bg(width: int, height: int, fill: str = "white") -> str:
    return f'<rect width="{width}" height="{height}" fill="{fill}"/>'


def svg_rect(x: int, y: int, w: int, h: int, fill: str, stroke: str = None, rx: int = 0) -> str:
    s = f'<rect x="{x}" y="{y}" width="{w}" height="{h}" fill="{fill}"'
    if stroke:
        s += f' stroke="{stroke}" stroke-width="1"'
    if rx:
        s += f' rx="{rx}"'
    return s + "/>"


def svg_text(x: int, y: int, text: str, size: int = 12, anchor: str = "start",
             color: str = DARK, weight: str = "normal", style: str = "normal",
             font: str = FONT_MONO) -> str:
    return (f'<text x="{x}" y="{y}" font-family="{font}" font-size="{size}" '
            f'fill="{color}" text-anchor="{anchor}" font-weight="{weight}" font-style="{style}">{text}</text>')


def svg_line(x1: int, y1: int, x2: int, y2: int, color: str = BORDER, width: float = 1) -> str:
    return f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="{color}" stroke-width="{width}"/>'


def svg_arrow_marker(id: str = "arrowhead", color: str = ARROW) -> str:
    return f'''  <defs>
    <marker id="{id}" markerWidth="10" markerHeight="7" refX="9" refY="3.5" orient="auto">
      <polygon points="0 0, 10 3.5, 0 7" fill="{color}"/>
    </marker>
  </defs>'''


def generate_typst_styles(output_path: Path) -> None:
    lines = [
        "// Auto-generated from styles.toml - do not edit directly",
        "",
        "// Colors",
    ]
    for name, value in _styles["colors"].items():
        typst_name = name.replace("-", "_")
        lines.append(f'#let color-{typst_name} = rgb("{value}")')
    lines.append("")
    output_path.write_text("\n".join(lines))


@dataclass
class Grid:
    rows: int
    cols: int
    cells: list

    @classmethod
    def from_coords(cls, rows: int, cols: int, coords: list):
        cells = [[False] * cols for _ in range(rows)]
        for i, j in coords:
            cells[i][j] = True
        return cls(rows, cols, cells)

    def __getitem__(self, idx):
        return self.cells[idx]
