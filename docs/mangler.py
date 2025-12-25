#!/usr/bin/env python3
"""
Transmutes the escaped LaTeX runes into mitex incantations that typst can parse without going mad.

This file is a shoggoth: a shapeless horror of regex substitutions that exists only because
mdbook-typst believes that best effort is good enough, regex can fix anything with sufficient
pain, and nothing is sacred.
"""

import argparse
import re
import shutil
import sys
from pathlib import Path


def add_preamble(content: str, preamble_path: Path) -> str:
    """Prepend the external preamble file with custom styling."""
    if '#import "@preview/mitex' not in content[:500]:
        preamble = preamble_path.read_text(encoding='utf-8')
        return preamble + "\n" + content
    return content


def fix_alerts(content: str) -> str:
    """
    Convert GitHub-style alerts to note-me package admonitions.

    Supported types: TIP, NOTE, WARNING, CAUTION, IMPORTANT
    Input:  #quote(block: true, quotes: auto,)[#par()[[!TIP] content...]]
    Output: #tip[content...]
    """
    def replace_alert(match):
        alert_type = match.group(1).lower()
        alert_content = match.group(2).strip()
        # note-me uses these function names directly
        return f'#{alert_type}[{alert_content}]'

    # Match #quote(block: true, quotes: auto,)[#par()[[!TYPE] content]]
    pattern = r'#quote\(block: true, quotes: auto,\)\[#par\(\)\[\[!(TIP|NOTE|WARNING|CAUTION|IMPORTANT)\]\s*(.+?)\]\s*\]'
    content = re.sub(pattern, replace_alert, content, flags=re.DOTALL | re.IGNORECASE)

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


def fix_headings(content: str) -> str:
    """
    Ensure headings start at the beginning of a line.

    mdbook-typst sometimes outputs #v(1em)==== Heading which breaks
    heading parsing since typst requires headings at line start.
    """
    # Match #v(...) immediately followed by heading markers (=+)
    pattern = r'(#v\([^)]+\))(=+)'
    content = re.sub(pattern, r'\1\n\2', content)
    return content


def fix_horizontal_rules(content: str) -> str:
    """
    Replace plain horizontal rules with styled separators.

    mdbook-typst outputs #line(length: 100%) for --- in markdown.
    Replace with a centered, shorter, lighter line for better typography.
    """
    # Match standalone horizontal rule lines
    pattern = r'^#line\(length: 100%\)$'
    styled_hr = r'''#v(1.5em)
#align(center)[#line(length: 30%, stroke: 0.75pt + luma(180))]
#v(1.5em)'''
    content = re.sub(pattern, styled_hr, content, flags=re.MULTILINE)
    return content


def fix_chapter_pagebreaks(content: str) -> str:
    """
    Add pagebreaks before chapter headings (level 2).

    In this book structure:
    - Level 1 (=) are intro sections and Arc dividers
    - Level 2 (==) are actual chapters within arcs

    We insert pagebreaks before level 2 headings so chapters start on new pages.
    """
    lines = content.split('\n')
    result = []
    chapter_count = 0

    for line in lines:
        # Match level 2 headings: == Title (not = or ===)
        if re.match(r'^== [^=]', line):
            chapter_count += 1
            # Add pagebreak before each chapter
            if chapter_count > 0:
                result.append('#pagebreak()')
        result.append(line)

    return '\n'.join(result)


def fix_display_in_paragraphs(content: str) -> str:
    """
    Move #mitex() calls out of #par() blocks.

    mitex display math is a block element and cannot be inside paragraphs.
    We need to split paragraphs around display math.
    """
    lines = content.split('\n')
    result = []

    mitex_pattern = re.compile(r'#mitex\(`[^`]+`\)')

    for line in lines:
        if '#par()[' in line and '#mitex(`' in line:
            # Find all mitex calls in this line
            mitex_calls = mitex_pattern.findall(line)

            if mitex_calls:
                # Split the line around mitex calls
                parts = mitex_pattern.split(line)
                output_parts = []

                for i, part in enumerate(parts):
                    # Clean up the part
                    part = part.strip()

                    if part.startswith('#par()['):
                        part = part[7:]  # Remove #par()[
                    if part.endswith(']'):
                        part = part[:-1]  # Remove trailing ]

                    part = part.strip()

                    if part:
                        output_parts.append(f'#par()[{part}]')

                    # Add the mitex call after this part (if there is one)
                    if i < len(mitex_calls):
                        output_parts.append(mitex_calls[i])

                result.extend(output_parts)
            else:
                result.append(line)
        else:
            result.append(line)

    return '\n'.join(result)


def main():
    parser = argparse.ArgumentParser(description='Post-process mdbook-typst output for LaTeX math support')
    parser.add_argument('--typst-dir', type=str, default='book/typst',
                        help='Path to typst output directory (default: book/typst)')
    args = parser.parse_args()

    # Determine paths relative to script location
    script_dir = Path(__file__).parent
    typst_dir = script_dir / args.typst_dir
    typst_file = typst_dir / 'book.typst'
    preamble_file = script_dir / 'preamble.typst'  # Source file, not in generated output

    if not typst_file.exists():
        print(f"Error: {typst_file} does not exist", file=sys.stderr)
        print("Run 'mdbook build' first to generate the typst file", file=sys.stderr)
        sys.exit(1)

    if not preamble_file.exists():
        print(f"Error: {preamble_file} does not exist", file=sys.stderr)
        sys.exit(1)

    # Copy assets needed by preamble to typst output directory
    beaver_src = script_dir / 'src' / 'beaver.png'
    beaver_dst = typst_dir / 'beaver.png'
    if beaver_src.exists():
        print(f"Copying {beaver_src.name} to typst directory...")
        shutil.copy2(beaver_src, beaver_dst)

    # Copy images directory for figures (lambda cube, etc.)
    images_src = script_dir / 'src' / 'images'
    images_dst = typst_dir / 'images'
    if images_src.exists():
        print(f"Copying images directory to typst directory...")
        if images_dst.exists():
            shutil.rmtree(images_dst)
        shutil.copytree(images_src, images_dst)

    print(f"Reading {typst_file}...")
    content = typst_file.read_text(encoding='utf-8')
    original_size = len(content)

    print("Adding preamble with title page and styling...")
    content = add_preamble(content, preamble_file)

    print("Converting alerts to note-me admonitions...")
    content = fix_alerts(content)

    print(r"Converting display math (\[...\]) to #mitex()...")
    content = fix_display_math(content)

    print(r"Converting inline math (\$...\$) to #mi()...")
    content = fix_inline_math(content)

    print("Restructuring paragraphs with display math...")
    content = fix_display_in_paragraphs(content)

    print("Fixing heading line positions...")
    content = fix_headings(content)

    print("Styling horizontal rules...")
    content = fix_horizontal_rules(content)

    print("Adding chapter pagebreaks...")
    content = fix_chapter_pagebreaks(content)

    print(f"Writing fixed content back to {typst_file}...")
    typst_file.write_text(content, encoding='utf-8')

    print(f"\nDone! Processed {original_size:,} bytes.")
    print("Math is now handled by mitex (LaTeX-in-Typst).")
    print("\nCompile the PDF with:")
    print(f"  cd {typst_file.parent}")
    print(f"  typst compile book.typst book.pdf")


if __name__ == '__main__':
    main()
