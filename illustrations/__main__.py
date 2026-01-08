import sys
from pathlib import Path

from . import gameoflife, hierarchy, tactics, lambdacube, proofstate
from .core import generate_typst_styles


def main():
    output_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("docs/src/images")
    gameoflife.generate(output_dir)
    hierarchy.generate(output_dir)
    tactics.generate(output_dir)
    lambdacube.generate_lambda_cube(output_dir)
    proofstate.generate(output_dir)
    styles_path = Path(__file__).parent.parent / "docs" / "styles.typst"
    generate_typst_styles(styles_path)
    print(f"Generated {styles_path}")


if __name__ == "__main__":
    main()
