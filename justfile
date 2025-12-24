default:
    @just --list

build:
    lake build

test:
    lake test

run:
    lake exe driver

clean:
    lake clean
    rm -rf .lake

serve:
    cd docs && mdbook serve --open

build-lean-docs:
    lake script run docs

install-mdbook:
    cargo install mdbook
    cargo install mdbook-katex

build-docs:
    cd docs && mdbook build

pdf:
    #!/usr/bin/env bash
    set -e
    cd docs
    rm -rf book/pdf
    cp book-typst.toml book.toml
    mdbook build
    cp book-html.toml book.toml
    python3 mangler.py --typst-dir book/pdf
    cd book/pdf && typst compile book.typst book.pdf
    echo "PDF written to docs/book/pdf/book.pdf"
    open book.pdf

clean-docs:
    rm -rf docs/book
    rm -rf docbuild/.lake

update:
    lake update

stats:
    @echo "=== Project Statistics ==="
    @echo "Lean files:"
    @find src -name "*.lean" | wc -l
    @echo "Total lines of Lean code:"
    @find src -name "*.lean" -exec wc -l {} + | tail -n 1
    @echo "Test files:"
    @find test -name "*.lean" 2>/dev/null | wc -l
    @echo "Documentation chapters:"
    @find docs/src -name "chapter_*.md" 2>/dev/null | wc -l

all: build build-docs
    @echo "All builds complete!"
