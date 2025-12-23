#!/usr/bin/env python3
"""Transmutes the escaped LaTeX runes into mitex incantations that typst can parse without going mad."""

import re
import sys
from pathlib import Path


def add_mitex_import(content: str) -> str:
    """Add mitex import at the top of the file if not present."""
    import_line = '#import "@preview/mitex:0.2.6": *\n'
    if 'mitex' not in content[:1000]:
        return import_line + content
    return content


def fix_display_math(content: str) -> str:
    r"""
    Convert display math to #mitex(`...`)

    Two patterns exist in mdbook-typst output:
    1. \$\$...\$\$ (from markdown $$...$$)
    2. \[...\] (from markdown \[...\])
    """
    def replace_display(match):
        latex = match.group(1).strip()
        # Unescape characters that mdbook-typst escaped
        latex = latex.replace(r'\_', '_')
        latex = latex.replace(r'\<', '<')
        latex = latex.replace(r'\>', '>')
        latex = latex.replace(r'\#', '#')
        latex = latex.replace(r'\@', '@')
        return f'#mitex(`{latex}`)'

    # Pattern 1: \$\$...\$\$
    content = re.sub(r'\\\$\\\$(.+?)\\\$\\\$', replace_display, content, flags=re.DOTALL)

    # Pattern 2: \[...\]
    content = re.sub(r'\\\[(.+?)\\\]', replace_display, content, flags=re.DOTALL)

    return content


def fix_inline_math(content: str) -> str:
    r"""
    Convert inline math \$...\$ to #mi(`...`)

    In the raw typst output, inline math from $...$ appears as \$...\$
    """
    # Match \$...\$ but not \$\$ (display math) or single \$ (literal)
    pattern = r'\\\$([^\$]+?)\\\$'

    def replace_inline(match):
        latex = match.group(1)
        # Unescape characters that mdbook-typst escaped
        latex = latex.replace(r'\_', '_')
        latex = latex.replace(r'\<', '<')
        latex = latex.replace(r'\>', '>')
        latex = latex.replace(r'\#', '#')
        latex = latex.replace(r'\@', '@')
        return f'#mi(`{latex}`)'

    return re.sub(pattern, replace_inline, content)


def fix_display_in_paragraphs(content: str) -> str:
    """
    Move #mitex() calls out of #par() blocks.

    mitex display math is a block element and cannot be inside paragraphs.
    We need to split paragraphs around display math.
    """
    # Find #par()[...#mitex(...)...] and restructure
    # This is a simplified approach - split at #mitex boundaries

    lines = content.split('\n')
    result = []

    for line in lines:
        if '#par()[' in line and '#mitex(`' in line:
            # This paragraph contains display math - need to split it
            # Pattern: #par()[text before #mitex(`...`) text after]

            # Extract parts
            match = re.match(r'(#par\(\)\[)(.*?)(#mitex\(`[^`]+`\))(.*?)(\])?$', line)
            if match:
                prefix = match.group(1)
                before = match.group(2).strip()
                mitex_call = match.group(3)
                after = match.group(4).strip() if match.group(4) else ''

                if before:
                    result.append(f'{prefix}{before}]')
                result.append(mitex_call)
                if after:
                    result.append(f'{prefix}{after}]')
            else:
                # Complex case - multiple mitex or nested structure
                # Just output as-is and hope for the best
                result.append(line)
        else:
            result.append(line)

    return '\n'.join(result)


def main():
    typst_file = Path('/Users/sdiehl/Git/hitchhiker-lean/docs/book/typst/book.typst')

    if not typst_file.exists():
        print(f"Error: {typst_file} does not exist", file=sys.stderr)
        print("Run 'mdbook build' first to generate the typst file", file=sys.stderr)
        sys.exit(1)

    print(f"Reading {typst_file}...")
    content = typst_file.read_text(encoding='utf-8')
    original_size = len(content)

    print("Adding mitex import...")
    content = add_mitex_import(content)

    print("Converting display math (\\[...\\]) to #mitex()...")
    content = fix_display_math(content)

    print("Converting inline math (\\$...\\$) to #mi()...")
    content = fix_inline_math(content)

    print("Restructuring paragraphs with display math...")
    content = fix_display_in_paragraphs(content)

    print(f"Writing fixed content back to {typst_file}...")
    typst_file.write_text(content, encoding='utf-8')

    print(f"\nDone! Processed {original_size:,} bytes.")
    print("Math is now handled by mitex (LaTeX-in-Typst).")
    print("\nCompile the PDF with:")
    print(f"  cd {typst_file.parent}")
    print(f"  typst compile book.typst book.pdf")


if __name__ == '__main__':
    main()
