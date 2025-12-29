from pathlib import Path
from .core import Grid, svg_header, svg_bg, svg_rect, svg_text, DARK, LIGHT, BORDER, ARROW, TEXT, FONT_SANS

CELL_SIZE = 28
CELL_RADIUS = 4
PADDING = 8


def step(grid: Grid) -> Grid:
    rows, cols = grid.rows, grid.cols

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

    new_cells = []
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
        new_cells.append(row)

    return Grid(rows, cols, new_cells)


def single_grid_svg(grid: Grid) -> str:
    width = grid.cols * CELL_SIZE + 2 * PADDING
    height = grid.rows * CELL_SIZE + 2 * PADDING

    lines = [svg_header(width, height), svg_bg(width, height)]

    for i in range(grid.rows):
        for j in range(grid.cols):
            x = PADDING + j * CELL_SIZE
            y = PADDING + i * CELL_SIZE
            fill = DARK if grid[i][j] else LIGHT
            lines.append(svg_rect(x, y, CELL_SIZE, CELL_SIZE, fill, BORDER, CELL_RADIUS))

    lines.append("</svg>")
    return "\n".join(lines)


def multi_grid_svg(grids: list, labels: list = None) -> str:
    if not grids:
        return ""

    rows, cols = grids[0].rows, grids[0].cols
    grid_width = cols * CELL_SIZE + 2 * PADDING
    grid_height = rows * CELL_SIZE + 2 * PADDING
    arrow_width = 30
    label_height = 24

    total_width = len(grids) * grid_width + (len(grids) - 1) * arrow_width
    total_height = grid_height + label_height

    lines = [
        svg_header(total_width, total_height),
        svg_bg(total_width, total_height),
        f'<style>text {{ font-family: {FONT_SANS}; font-size: 12px; fill: {TEXT}; }}</style>',
    ]

    for idx, grid in enumerate(grids):
        offset_x = idx * (grid_width + arrow_width)

        if labels and idx < len(labels):
            label_x = offset_x + grid_width // 2
            lines.append(f'<text x="{label_x}" y="16" text-anchor="middle">{labels[idx]}</text>')

        for i in range(rows):
            for j in range(cols):
                x = offset_x + PADDING + j * CELL_SIZE
                y = label_height + PADDING + i * CELL_SIZE
                fill = DARK if grid[i][j] else LIGHT
                lines.append(svg_rect(x, y, CELL_SIZE, CELL_SIZE, fill, BORDER, CELL_RADIUS))

        if idx < len(grids) - 1:
            arrow_x = offset_x + grid_width + arrow_width // 2
            arrow_y = label_height + grid_height // 2
            lines.append(
                f'<path d="M {arrow_x - 8} {arrow_y} L {arrow_x + 8} {arrow_y} '
                f'M {arrow_x + 4} {arrow_y - 4} L {arrow_x + 8} {arrow_y} L {arrow_x + 4} {arrow_y + 4}" '
                f'stroke="{ARROW}" stroke-width="2" fill="none"/>'
            )

    lines.append("</svg>")
    return "\n".join(lines)


BLINKER = Grid.from_coords(5, 5, [(1, 2), (2, 2), (3, 2)])
BLOCK = Grid.from_coords(4, 4, [(1, 1), (1, 2), (2, 1), (2, 2)])
GLIDER = Grid.from_coords(6, 6, [(0, 1), (1, 2), (2, 0), (2, 1), (2, 2)])
NEIGHBORS = Grid.from_coords(3, 3, [(1, 1)])


def generate(output_dir: Path):
    output_dir.mkdir(parents=True, exist_ok=True)

    (output_dir / "gol_neighbors.svg").write_text(single_grid_svg(NEIGHBORS))
    (output_dir / "gol_block.svg").write_text(single_grid_svg(BLOCK))

    blinker_gens = [BLINKER, step(BLINKER)]
    (output_dir / "gol_blinker.svg").write_text(
        multi_grid_svg(blinker_gens, ["Gen 0", "Gen 1"])
    )

    glider_gens = [GLIDER]
    g = GLIDER
    for _ in range(4):
        g = step(g)
        glider_gens.append(g)
    (output_dir / "gol_glider.svg").write_text(
        multi_grid_svg(glider_gens, [f"Gen {i}" for i in range(5)])
    )

    print(f"Generated Game of Life SVGs in {output_dir}")
