# Build System

```bash
# macOS dependencies
brew install just typst
cargo install mdbook --version 0.4.52
cargo install mdbook-typst
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

The HTML and PDF outputs use separate toolchains due to compatibility constraints. HTML is built with mdbook 0.5.2, which supports GitHub-style admonitions (`[!TIP]`, `[!NOTE]`, etc.) that render as styled callout boxes. PDF generation requires mdbook-typst, which only works with mdbook 0.4.52 due to breaking changes in the RenderContext serialization format. The CI workflow handles this by building HTML first with the newer mdbook, then downgrading to build the typst output. Two configuration files control this: [`book.toml`](docs/book.toml) (HTML only) and [`book-typst.toml`](docs/book-typst.toml) (typst only).

The PDF pipeline has an additional post-processing step. The mdbook-typst renderer escapes LaTeX math delimiters and special characters in ways that break typst compilation. The [evil mangler](docs/mangler.py) fixes this by converting escaped math (`\$...\$` and `\[...\]`) to mitex function calls (`#mi()` and `#mitex()`), which use the mitex package to render LaTeX math natively in typst. It ain't pretty but it works. The script also prepends a preamble ([`preamble.typst`](docs/preamble.typst)) containing the title page, legal notice, document styling, theorem environments, admonition boxes, and running headers. After mangling, typst compiles the result to PDF. Run `just pdf` locally or push to main to trigger the full CI build.

Illustrations are procedurally generated rather than hand-drawn. The script [`scripts/life_viz.py`](scripts/life_viz.py) produces SVGs for Game of Life patterns, the universe hierarchy tower, the algebraic structure lattice, and tactic proof state diagrams. Colors live in [`scripts/colors.py`](scripts/colors.py) so the palette stays consistent across figures. This approach keeps illustrations reproducible, diff-friendly, and immune to the "I'll just tweak this one pixel" death spiral that consumes graphic designers and theoretical physicists alike. Run `just gen-svg` to regenerate all images, or let `just build-docs` handle it automatically.
