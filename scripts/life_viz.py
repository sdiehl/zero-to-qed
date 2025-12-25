"""Generate SVG visualizations for From Zero to QED."""

from pathlib import Path
import sys
from colors import DARK, LIGHT, BORDER, ARROW, ACCENT, PROP, TYPE, TEXT

CELL_SIZE = 28
CELL_RADIUS = 4
PADDING = 8

def step(grid):
    rows, cols = len(grid), len(grid[0])
    def count_neighbors(i, j):
        total = 0
        for di in [-1, 0, 1]:
            for dj in [-1, 0, 1]:
                if di == 0 and dj == 0:
                    continue
                ni, nj = (i + di) % rows, (j + dj) % cols
                if grid[ni][nj]:
                    total += 1
        return total

    new_grid = []
    for i in range(rows):
        row = []
        for j in range(cols):
            neighbors = count_neighbors(i, j)
            alive = grid[i][j]
            if alive and neighbors in [2, 3]:
                row.append(True)
            elif not alive and neighbors == 3:
                row.append(True)
            else:
                row.append(False)
        new_grid.append(row)
    return new_grid

def grid_to_svg(grid, cell_size=CELL_SIZE):
    rows, cols = len(grid), len(grid[0])
    width = cols * cell_size + 2 * PADDING
    height = rows * cell_size + 2 * PADDING

    lines = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}">',
        f'  <rect width="{width}" height="{height}" fill="white"/>',
    ]

    for i in range(rows):
        for j in range(cols):
            x = PADDING + j * cell_size
            y = PADDING + i * cell_size
            fill = DARK if grid[i][j] else LIGHT
            lines.append(
                f'  <rect x="{x}" y="{y}" width="{cell_size}" height="{cell_size}" '
                f'fill="{fill}" stroke="{BORDER}" stroke-width="1" rx="{CELL_RADIUS}"/>'
            )

    lines.append('</svg>')
    return '\n'.join(lines)

def multi_generation_svg(grids, labels=None):
    if not grids:
        return ""

    rows, cols = len(grids[0]), len(grids[0][0])
    grid_width = cols * CELL_SIZE + 2 * PADDING
    grid_height = rows * CELL_SIZE + 2 * PADDING
    arrow_width = 30
    label_height = 24

    total_width = len(grids) * grid_width + (len(grids) - 1) * arrow_width
    total_height = grid_height + label_height

    lines = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{total_width}" height="{total_height}">',
        f'  <rect width="{total_width}" height="{total_height}" fill="white"/>',
        f'  <style>text {{ font-family: system-ui, sans-serif; font-size: 12px; fill: {TEXT}; }}</style>',
    ]

    for idx, grid in enumerate(grids):
        offset_x = idx * (grid_width + arrow_width)

        if labels and idx < len(labels):
            label_x = offset_x + grid_width // 2
            lines.append(f'  <text x="{label_x}" y="16" text-anchor="middle">{labels[idx]}</text>')

        for i in range(rows):
            for j in range(cols):
                x = offset_x + PADDING + j * CELL_SIZE
                y = label_height + PADDING + i * CELL_SIZE
                fill = DARK if grid[i][j] else LIGHT
                lines.append(
                    f'  <rect x="{x}" y="{y}" width="{CELL_SIZE}" height="{CELL_SIZE}" '
                    f'fill="{fill}" stroke="{BORDER}" stroke-width="1" rx="{CELL_RADIUS}"/>'
                )

        if idx < len(grids) - 1:
            arrow_x = offset_x + grid_width + arrow_width // 2
            arrow_y = label_height + grid_height // 2
            lines.append(
                f'  <path d="M {arrow_x - 8} {arrow_y} L {arrow_x + 8} {arrow_y} '
                f'M {arrow_x + 4} {arrow_y - 4} L {arrow_x + 8} {arrow_y} L {arrow_x + 4} {arrow_y + 4}" '
                f'stroke="{ARROW}" stroke-width="2" fill="none"/>'
            )

    lines.append('</svg>')
    return '\n'.join(lines)

def make_grid(rows, cols, cells):
    grid = [[False] * cols for _ in range(rows)]
    for i, j in cells:
        grid[i][j] = True
    return grid

BLINKER = make_grid(5, 5, [(1, 2), (2, 2), (3, 2)])
BLOCK = make_grid(4, 4, [(1, 1), (1, 2), (2, 1), (2, 2)])
GLIDER = make_grid(6, 6, [(0, 1), (1, 2), (2, 0), (2, 1), (2, 2)])
NEIGHBORS_DEMO = make_grid(3, 3, [(1, 1)])

def universe_hierarchy_svg():
    width, height = 400, 320
    box_w, box_h = 100, 36
    center_x = width // 2

    levels = [
        ("Prop", PROP, "Sort 0"),
        ("Type", TYPE, "Sort 1"),
        ("Type 1", TYPE, "Sort 2"),
        ("Type 2", TYPE, "Sort 3"),
    ]

    lines = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}">',
        f'  <rect width="{width}" height="{height}" fill="white"/>',
        '  <defs>',
        '    <marker id="arrowhead" markerWidth="10" markerHeight="7" refX="9" refY="3.5" orient="auto">',
        f'      <polygon points="0 0, 10 3.5, 0 7" fill="{ARROW}"/>',
        '    </marker>',
        '  </defs>',
        f'  <style>',
        f'    .level {{ font-family: ui-monospace, monospace; font-size: 14px; font-weight: bold; }}',
        f'    .sort {{ font-family: system-ui, sans-serif; font-size: 11px; fill: {TEXT}; }}',
        f'    .label {{ font-family: system-ui, sans-serif; font-size: 12px; fill: {TEXT}; }}',
        f'  </style>',
    ]

    for i, (name, color, sort) in enumerate(levels):
        y = height - 50 - i * 70
        x = center_x - box_w // 2

        lines.append(
            f'  <rect x="{x}" y="{y}" width="{box_w}" height="{box_h}" '
            f'fill="{color}" rx="6" opacity="0.9"/>'
        )
        lines.append(
            f'  <text x="{center_x}" y="{y + 23}" text-anchor="middle" fill="white" class="level">{name}</text>'
        )
        lines.append(
            f'  <text x="{x + box_w + 12}" y="{y + 23}" class="sort">{sort}</text>'
        )

        if i < len(levels) - 1:
            arrow_y1 = y
            arrow_y2 = y - 34
            lines.append(
                f'  <line x1="{center_x}" y1="{arrow_y1}" x2="{center_x}" y2="{arrow_y2}" '
                f'stroke="{ARROW}" stroke-width="2" marker-end="url(#arrowhead)"/>'
            )

    lines.append(f'  <text x="{center_x}" y="38" text-anchor="middle" class="label">⋮</text>')
    lines.append(f'  <text x="30" y="{height - 35}" class="label">Propositions</text>')
    lines.append(f'  <text x="30" y="{height - 105}" class="label">Data types</text>')
    lines.append(
        f'  <text x="{center_x - box_w//2 - 10}" y="{height - 27}" '
        f'text-anchor="end" class="sort" font-style="italic">impredicative</text>'
    )

    lines.append('</svg>')
    return '\n'.join(lines)

def algebra_hierarchy_svg():
    width, height = 500, 380

    structures = {
        "Semigroup": (100, 320, DARK),
        "Monoid": (100, 240, DARK),
        "Group": (100, 160, DARK),
        "CommGroup": (50, 80, ACCENT),
        "Ring": (200, 80, ACCENT),
        "CommRing": (125, 20, TYPE),
        "Field": (275, 20, PROP),
        "AddMonoid": (350, 240, DARK),
        "AddGroup": (350, 160, DARK),
        "Module": (400, 80, ACCENT),
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
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}">',
        f'  <rect width="{width}" height="{height}" fill="white"/>',
        '  <defs>',
        '    <marker id="arr" markerWidth="8" markerHeight="6" refX="7" refY="3" orient="auto">',
        f'      <polygon points="0 0, 8 3, 0 6" fill="{ARROW}"/>',
        '    </marker>',
        '  </defs>',
        f'  <style>.struct {{ font-family: ui-monospace, monospace; font-size: 11px; font-weight: 500; }}</style>',
    ]

    for src, dst in edges:
        x1, y1, _ = structures[src]
        x2, y2, _ = structures[dst]
        dx, dy = x2 - x1, y2 - y1
        dist = (dx**2 + dy**2) ** 0.5
        if dist > 0:
            ux, uy = dx / dist, dy / dist
            x1 += ux * 35
            y1 += uy * 12
            x2 -= ux * 35
            y2 -= uy * 12
        lines.append(
            f'  <line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" '
            f'stroke="{BORDER}" stroke-width="1.5" marker-end="url(#arr)"/>'
        )

    for name, (x, y, color) in structures.items():
        box_w = len(name) * 8 + 16
        box_h = 24
        rx = x - box_w // 2
        ry = y - box_h // 2
        lines.append(
            f'  <rect x="{rx}" y="{ry}" width="{box_w}" height="{box_h}" fill="{color}" rx="4"/>'
        )
        lines.append(
            f'  <text x="{x}" y="{y + 4}" text-anchor="middle" fill="white" class="struct">{name}</text>'
        )

    lines.append(f'  <text x="420" y="320" font-family="system-ui" font-size="10" fill="{TEXT}">Basic</text>')
    lines.append(f'  <rect x="400" y="310" width="12" height="12" fill="{DARK}" rx="2"/>')
    lines.append(f'  <text x="420" y="340" font-family="system-ui" font-size="10" fill="{TEXT}">With Ring</text>')
    lines.append(f'  <rect x="400" y="330" width="12" height="12" fill="{ACCENT}" rx="2"/>')
    lines.append(f'  <text x="420" y="360" font-family="system-ui" font-size="10" fill="{TEXT}">Field</text>')
    lines.append(f'  <rect x="400" y="350" width="12" height="12" fill="{PROP}" rx="2"/>')

    lines.append('</svg>')
    return '\n'.join(lines)

def generate_all(output_dir):
    output_dir.mkdir(parents=True, exist_ok=True)

    with open(output_dir / "gol_neighbors.svg", "w") as f:
        f.write(grid_to_svg(NEIGHBORS_DEMO))

    blinker_1 = step(BLINKER)
    with open(output_dir / "gol_blinker.svg", "w") as f:
        f.write(multi_generation_svg([BLINKER, blinker_1], ["Gen 0", "Gen 1"]))

    with open(output_dir / "gol_block.svg", "w") as f:
        f.write(grid_to_svg(BLOCK))

    glider_gens = [GLIDER]
    g = GLIDER
    for _ in range(4):
        g = step(g)
        glider_gens.append(g)
    with open(output_dir / "gol_glider.svg", "w") as f:
        f.write(multi_generation_svg(glider_gens, [f"Gen {i}" for i in range(5)]))

    with open(output_dir / "universe_hierarchy.svg", "w") as f:
        f.write(universe_hierarchy_svg())

    with open(output_dir / "algebra_hierarchy.svg", "w") as f:
        f.write(algebra_hierarchy_svg())

    print(f"Generated SVGs in {output_dir}")

if __name__ == "__main__":
    generate_all(Path(sys.argv[1]) if len(sys.argv) > 1 else Path("docs/src/images"))
