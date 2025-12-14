#!/usr/bin/env python3
"""
Build PDF from mdbook markdown sources using pandoc and xelatex.

Handles:
- mdbook {{#include path:anchor}} directives
- Math notation conversion (\\( \\) -> $ $)
- mdbook callouts (> [!NOTE], etc.)
- Chapter ordering from SUMMARY.md

Requirements:
- pandoc: brew install pandoc
- xelatex: brew install --cask mactex (or basictex)
- fonts: TeX Gyre Pagella, JetBrains Mono (optional, will fallback)
"""

import re
import shutil
import subprocess
import sys
from pathlib import Path


def check_dependencies():
    """Check that required tools are installed."""
    missing = []
    if not shutil.which("pandoc"):
        missing.append("pandoc (brew install pandoc)")
    if not shutil.which("xelatex"):
        missing.append("xelatex (brew install --cask mactex)")

    if missing:
        print("Missing dependencies:", file=sys.stderr)
        for dep in missing:
            print(f"  - {dep}", file=sys.stderr)
        sys.exit(1)

ROOT = Path(__file__).parent.parent
DOCS_SRC = ROOT / "docs" / "src"
OUTPUT = ROOT / "docs" / "zero-to-qed.pdf"


def extract_anchor(filepath: Path, anchor: str) -> str:
    """Extract content between ANCHOR: name and ANCHOR_END: name markers."""
    content = filepath.read_text()

    # Pattern for Lean anchor comments
    start_pattern = rf"--\s*ANCHOR:\s*{re.escape(anchor)}\s*\n"
    end_pattern = rf"--\s*ANCHOR_END:\s*{re.escape(anchor)}"

    start_match = re.search(start_pattern, content)
    if not start_match:
        print(f"Warning: Anchor '{anchor}' not found in {filepath}", file=sys.stderr)
        return f"-- Anchor '{anchor}' not found"

    end_match = re.search(end_pattern, content[start_match.end():])
    if not end_match:
        print(f"Warning: End anchor for '{anchor}' not found in {filepath}", file=sys.stderr)
        return content[start_match.end():]

    return content[start_match.end():start_match.end() + end_match.start()].strip()


def expand_includes(content: str, base_path: Path) -> str:
    """Expand {{#include path:anchor}} directives."""
    pattern = r'\{\{#include\s+([^}:]+)(?::([^}]+))?\}\}'

    def replace_include(match):
        rel_path = match.group(1).strip()
        anchor = match.group(2).strip() if match.group(2) else None

        # Resolve path relative to the markdown file
        full_path = (base_path / rel_path).resolve()

        if not full_path.exists():
            print(f"Warning: Include file not found: {full_path}", file=sys.stderr)
            return f"// File not found: {rel_path}"

        if anchor:
            return extract_anchor(full_path, anchor)
        else:
            return full_path.read_text()

    return re.sub(pattern, replace_include, content)


def convert_math(content: str) -> str:
    """Convert mdbook math notation to pandoc-compatible format."""
    # \\( ... \\) -> $...$  (inline math)
    content = re.sub(r'\\\\?\\\(', '$', content)
    content = re.sub(r'\\\\?\\\)', '$', content)
    # \\[ ... \\] -> $$...$$ (display math)
    content = re.sub(r'\\\\?\\\[', '$$', content)
    content = re.sub(r'\\\\?\\\]', '$$', content)
    return content


def escape_link_underscores(content: str) -> str:
    """Escape underscores in markdown link URLs to prevent LaTeX subscript interpretation."""
    # Match markdown links: [text](url)
    def escape_url(match):
        text = match.group(1)
        url = match.group(2)
        # Escape underscores in the URL
        escaped_url = url.replace('_', r'\_')
        return f'[{text}]({escaped_url})'

    return re.sub(r'\[([^\]]+)\]\(([^)]+)\)', escape_url, content)


def convert_callouts(content: str) -> str:
    """Convert mdbook callouts to LaTeX environments."""
    # > [!NOTE] -> \begin{note}...\end{note}
    # > [!TIP] -> \begin{tip}...\end{tip}
    # > [!WARNING] -> \begin{warning}...\end{warning}

    lines = content.split('\n')
    result = []
    in_callout = False
    callout_type = None
    callout_content = []

    for line in lines:
        # Check for callout start
        callout_match = re.match(r'>\s*\[!(NOTE|TIP|WARNING|IMPORTANT)\]', line)
        if callout_match:
            if in_callout:
                # Close previous callout
                result.append(f'\\end{{{callout_type.lower()}}}')
            callout_type = callout_match.group(1)
            in_callout = True
            result.append(f'\\begin{{{callout_type.lower()}}}')
            continue

        if in_callout:
            if line.startswith('>'):
                # Continue callout, strip the >
                result.append(line[1:].strip())
            else:
                # End callout
                result.append(f'\\end{{{callout_type.lower()}}}')
                in_callout = False
                callout_type = None
                result.append(line)
        else:
            result.append(line)

    # Close any remaining callout
    if in_callout:
        result.append(f'\\end{{{callout_type.lower()}}}')

    return '\n'.join(result)


def get_chapter_order() -> list[Path]:
    """Parse SUMMARY.md to get chapter order."""
    summary = DOCS_SRC / "SUMMARY.md"
    content = summary.read_text()

    chapters = []
    for match in re.finditer(r'\[.*?\]\(\./([^)]+\.md)\)', content):
        chapter_path = DOCS_SRC / match.group(1)
        if chapter_path.exists():
            chapters.append(chapter_path)

    return chapters


def preprocess_markdown(filepath: Path) -> str:
    """Preprocess a single markdown file."""
    content = filepath.read_text()
    content = expand_includes(content, filepath.parent)
    content = convert_math(content)
    content = convert_callouts(content)
    content = escape_link_underscores(content)
    return content


def build_combined_markdown() -> str:
    """Build a single combined markdown document."""
    chapters = get_chapter_order()

    parts = []

    # Add metadata header
    # Use fonts available on both macOS and Ubuntu CI
    parts.append("""---
title: "From Zero to QED"
subtitle: "An informal introduction to formality in Lean 4"
author: "Stephen Diehl"
documentclass: report
geometry: margin=1in
fontsize: 11pt
header-includes:
  - |
    \\usepackage{fancyhdr}
    \\usepackage{tcolorbox}
    \\newtcolorbox{note}{colback=blue!5,colframe=blue!50,title=Note}
    \\newtcolorbox{tip}{colback=green!5,colframe=green!50,title=Tip}
    \\newtcolorbox{warning}{colback=red!5,colframe=red!50,title=Warning}
    \\newtcolorbox{important}{colback=orange!5,colframe=orange!50,title=Important}
---

""")

    for chapter in chapters:
        print(f"Processing: {chapter.name}", file=sys.stderr)
        content = preprocess_markdown(chapter)
        parts.append(content)
        parts.append("\n\n")  # Ensure separation between chapters

    return ''.join(parts)


def build_pdf():
    """Build the PDF using pandoc."""
    check_dependencies()

    print("Building combined markdown...", file=sys.stderr)
    combined = build_combined_markdown()

    # Write intermediate file for debugging
    intermediate = ROOT / "docs" / "combined.md"
    intermediate.write_text(combined)
    print(f"Wrote intermediate markdown to {intermediate}", file=sys.stderr)

    print("Running pandoc...", file=sys.stderr)
    cmd = [
        "pandoc",
        str(intermediate),
        "-o", str(OUTPUT),
        "--pdf-engine=xelatex",
        "--toc",
        "--toc-depth=2",
        "--number-sections",
        "--highlight-style=tango",
        "-V", "colorlinks=true",
        "-V", "linkcolor=blue",
        "-V", "urlcolor=blue",
    ]

    result = subprocess.run(cmd, capture_output=True, text=True)

    if result.returncode != 0:
        print("Pandoc failed:", file=sys.stderr)
        print(result.stderr, file=sys.stderr)
        sys.exit(1)

    print(f"PDF written to {OUTPUT}", file=sys.stderr)


if __name__ == "__main__":
    build_pdf()
